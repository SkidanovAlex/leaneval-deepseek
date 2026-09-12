import Mathlib
import Submission.Sec3Core
import Submission.IntFun
import Submission.Commons.Analysis.Real.log_geom_decay_steps
import Submission.AuxSimpleAc

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Section 3 tower: recursion, prefixes, descendant sequences

Tikhomirov 2020, Section 3.  Building blocks of the refinement tower on top
of `Submission.Sec3Core`:

- `pre x k hk` restricts an integer vector on `Fin ℓ` to its first `k`
  coordinates;
- the embedding lemmas `upEmb`/`upIns`/`hA0_eq`/`hA1_eq` and the weight and
  subset-sum factorisations `wB_upEmb`, `wB_upIns`, `subSum_upEmb`,
  `subSum_upIns` under adding a coordinate;
- `avgF_rec` is the one-step recursion
  `f_{A,p,k+1}(t) = (1−p)·f_{A,p,k}(t) + p·f_{A,p,k}(t + xₖ)`
  (equation (eq: aux averaging) of the paper), proved by partitioning the
  averaging subsets into those avoiding/containing the last coordinate.

These are the primitives used by Lemma l:aux 09019847294 (descendant
sequences) and the rest of the refinement tower.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Measure

namespace Submission.Sec3Tower

open Submission.Sec3
open Submission.IntFun

/-- Restrict an integer vector on `Fin ℓ` to the first `k ≤ ℓ` coordinates. -/
def pre {ℓ : ℕ} (x : Fin ℓ → ℤ) (k : ℕ) (hk : k ≤ ℓ) : Fin k → ℤ :=
  fun j => x (Fin.castLE hk j)

/-- The last coordinate of `Fin (k+1)`. -/
def last {k : ℕ} : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩

/-- Embed `Finset (Fin k)` into subsets of `Fin (k+1)` avoiding `last`. -/
def upEmb {k : ℕ} (B : Finset (Fin k)) : Finset (Fin (k + 1)) :=
  B.image (Fin.castSucc)

/-- Embed plus `last`: `B ↦ B↑ ∪ {last}`. -/
def upIns {k : ℕ} (B : Finset (Fin k)) : Finset (Fin (k + 1)) :=
  insert last (upEmb B)

lemma castSucc_injective (k : ℕ) : Function.Injective (@Fin.castSucc k) := by
  intro a b hab
  apply Fin.ext
  simpa using (congrArg Fin.val hab)

/-- `last` is not in the range of `castSucc`. -/
lemma castSucc_ne_last {k : ℕ} (j : Fin k) : Fin.castSucc j ≠ (last : Fin (k + 1)) := by
  intro h
  have hval : (Fin.castSucc j).val = (last : Fin (k + 1)).val := congrArg Fin.val h
  dsimp [Fin.castSucc, last] at hval
  omega

/-- Elements of `Fin (k+1)` different from `last` come from `castSucc`. -/
lemma eq_castSucc_of_ne_last {k : ℕ} (j : Fin (k + 1)) (hj : j ≠ last) :
    ∃ j' : Fin k, Fin.castSucc j' = j := by
  have hjvalne : j.val ≠ k := by
    intro hv
    apply hj
    apply Fin.ext
    exact hv
  have hjval : j.val < k := by
    have : j.val < k + 1 := j.isLt
    omega
  refine ⟨⟨j.val, hjval⟩, ?_⟩
  apply Fin.ext
  simp

/-- Membership of `upEmb B`. -/
lemma mem_upEmb {k : ℕ} (B : Finset (Fin k)) (j : Fin k) :
    Fin.castSucc j ∈ upEmb B ↔ j ∈ B := by
  classical
  rw [upEmb, Finset.mem_image]
  constructor
  · intro h
    rcases h with ⟨j', hj', hEq⟩
    have : j' = j := (castSucc_injective k) hEq
    simpa [this] using hj'
  · intro hj
    exact ⟨j, hj, rfl⟩

/-- `last ∉ upEmb B`. -/
lemma last_not_mem_upEmb {k : ℕ} (B : Finset (Fin k)) : last ∉ upEmb B := by
  classical
  intro h
  rcases Finset.mem_image.mp h with ⟨j, hj, hEq⟩
  exact castSucc_ne_last j hEq

/-- `last ∈ upIns B`. -/
lemma last_mem_upIns {k : ℕ} (B : Finset (Fin k)) : last ∈ upIns B := by
  simp [upIns]

/-- Non-last members of `upIns B` come from `upEmb B`. -/
lemma upIns_mem {k : ℕ} (B : Finset (Fin k)) (j : Fin (k + 1)) (hj : j ≠ last) :
    j ∈ upIns B ↔ j ∈ upEmb B := by
  classical
  simp [upIns, hj]

/-- Sum over the embedded subset equals the sum over the original subset. -/
lemma subSum_upEmb {ℓ : ℕ} (x : Fin (ℓ + 1) → ℤ) (B : Finset (Fin ℓ)) :
    subSum x (upEmb B) = subSum (pre x ℓ (Nat.le_succ ℓ)) B := by
  classical
  dsimp [subSum, upEmb, pre]
  rw [Finset.sum_image]
  · rfl
  · intro a _ b _ hab
    exact (castSucc_injective ℓ) hab

/-- Sum over the embedded-plus-last subset. -/
lemma subSum_upIns {ℓ : ℕ} (x : Fin (ℓ + 1) → ℤ) (B : Finset (Fin ℓ)) :
    subSum x (upIns B) = subSum (pre x ℓ (Nat.le_succ ℓ)) B + x last := by
  classical
  change (∑ j ∈ upIns B, x j) = subSum (pre x ℓ (Nat.le_succ ℓ)) B + x last
  dsimp [upIns]
  rw [Finset.sum_insert (last_not_mem_upEmb B)]
  have hmid' : (∑ x_1 ∈ upEmb B, x x_1) = subSum (pre x ℓ (Nat.le_succ ℓ)) B := by
    simpa [subSum] using (subSum_upEmb (ℓ := ℓ) x B)
  rw [hmid']
  ring

/-- Weight of `upEmb B` at level `k+1` is `(1−p)` times the weight at level `k`. -/
lemma wB_upEmb {k : ℕ} (p : unitInterval) (B : Finset (Fin k)) :
    wB (k + 1) p (upEmb B) = (1 - (p : ℝ)) * wB k p B := by
  classical
  dsimp [wB, upEmb]
  have hcard : (B.image (Fin.castSucc)).card = B.card :=
    (Finset.card_image_iff.mpr (fun a ha b hb h => (castSucc_injective k) h))
  rw [hcard]
  have hle : B.card ≤ k := by simpa using B.card_le_univ
  have hpow : (1 - (p : ℝ)) ^ ((k + 1) - B.card) = (1 - (p : ℝ)) * (1 - (p : ℝ)) ^ (k - B.card) := by
    have hsub : (k + 1) - B.card = (k - B.card) + 1 := by omega
    rw [hsub, pow_succ']
  rw [hpow]
  ac_rfl

/-- Weight of `upIns B` at level `k+1` is `p` times the weight at level `k`. -/
lemma wB_upIns {k : ℕ} (p : unitInterval) (B : Finset (Fin k)) :
    wB (k + 1) p (upIns B) = (p : ℝ) * wB k p B := by
  classical
  have hcard : (upIns B).card = B.card + 1 := by
    dsimp [upIns]
    rw [Finset.card_insert_of_notMem (last_not_mem_upEmb B)]
    have hc : (upEmb B).card = B.card := by
      dsimp [upEmb]
      exact (Finset.card_image_iff.mpr (fun a ha b hb h => (castSucc_injective k) h))
    rw [hc]
  have hle : B.card ≤ k := by simpa using B.card_le_univ
  have hpow : (1 - (p : ℝ)) ^ ((k + 1) - (B.card + 1)) = (1 - (p : ℝ)) ^ (k - B.card) := by
    have hsub : (k + 1) - (B.card + 1) = k - B.card := by omega
    rw [hsub]
  calc
    wB (k + 1) p (upIns B)
        = (p : ℝ) ^ (upIns B).card * (1 - (p : ℝ)) ^ ((k + 1) - (upIns B).card) := by rfl
    _ = (p : ℝ) ^ (B.card + 1) * (1 - (p : ℝ)) ^ ((k + 1) - (upIns B).card) := by rw [hcard]
    _ = (p : ℝ) * (p : ℝ) ^ B.card * (1 - (p : ℝ)) ^ (k - B.card) := by
          rw [hcard]
          rw [hpow]
          ring_nf
    _ = (p : ℝ) * wB k p B := by
          dsimp [wB]
          ac_rfl


/-- The no-`last` subsets of `Fin (k+1)` are exactly the embeddings of subsets
of `Fin k`. -/
lemma hA0_eq {k : ℕ} :
    ((Finset.univ : Finset (Fin (k + 1))).powerset.filter
      (fun B : Finset (Fin (k + 1)) => last ∉ B)) =
      (Finset.univ : Finset (Fin k)).powerset.image (upEmb : Finset (Fin k) → Finset (Fin (k + 1))) := by
  classical
  ext B
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hB, hnot⟩
    let B' : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter
      (fun j : Fin k => Fin.castSucc j ∈ B)
    have hEq : B = upEmb B' := by
      ext j
      by_cases hjlast : j = last
      · subst hjlast
        constructor
        · intro hmem
          exact False.elim (hnot hmem)
        · intro hmem
          exact False.elim (last_not_mem_upEmb B' hmem)
      · rcases eq_castSucc_of_ne_last j hjlast with ⟨j', hjEq⟩
        rw [← hjEq]
        have hB' : j' ∈ B' ↔ Fin.castSucc j' ∈ B := by
          dsimp [B']
          simp
        rw [← hB']
        exact (mem_upEmb B' j').symm
    rw [hEq]
    exact Finset.mem_image.mpr ⟨B', by simp, rfl⟩
  · intro h
    rcases Finset.mem_image.mp h with ⟨B', hB', hEq⟩
    rw [← hEq]
    exact Finset.mem_filter.mpr ⟨by simp, last_not_mem_upEmb B'⟩

/-- The subsets containing `last` are exactly `upIns`-images of subsets of
`Fin k`. -/
lemma hA1_eq {k : ℕ} :
    ((Finset.univ : Finset (Fin (k + 1))).powerset.filter
      (fun B : Finset (Fin (k + 1)) => last ∈ B)) =
      (Finset.univ : Finset (Fin k)).powerset.image (upIns : Finset (Fin k) → Finset (Fin (k + 1))) := by
  classical
  ext B
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hB, hin⟩
    let B' : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter
      (fun j : Fin k => Fin.castSucc j ∈ B)
    have hEq : B = upIns B' := by
      ext j
      by_cases hjlast : j = last
      · subst hjlast
        simp [hin, last_mem_upIns B']
      · rcases eq_castSucc_of_ne_last j hjlast with ⟨j', hjEq⟩
        rw [← hjEq]
        have hB' : j' ∈ B' ↔ Fin.castSucc j' ∈ B := by
          dsimp [B']
          simp
        -- castSucc j' ∈ upIns B' ⟺ castSucc j' ∈ upEmb B' (j' ≠ last-case: castSucc j' ≠ last)
        have hne : Fin.castSucc j' ≠ last := castSucc_ne_last j'
        rw [upIns_mem B' (Fin.castSucc j') hne]
        -- castSucc j' ∈ upEmb B' ⟺ j' ∈ B'
        rw [mem_upEmb B' j']
        rw [hB']
    rw [hEq]
    exact Finset.mem_image.mpr ⟨B', by simp, rfl⟩
  · intro h
    rcases Finset.mem_image.mp h with ⟨B', hB', hEq⟩
    rw [← hEq]
    exact Finset.mem_filter.mpr ⟨by simp, last_mem_upIns B'⟩

/-- `upEmb` is injective on subsets. -/
lemma upEmb_injective_on {k : ℕ} :
    Set.InjOn (upEmb : Finset (Fin k) → Finset (Fin (k + 1)))
      ((Finset.univ : Finset (Fin k)).powerset : Set (Finset (Fin k))) := by
  classical
  intro B₁ hB₁ B₂ hB₂ hEq
  ext j
  have hiff : j ∈ B₁ ↔ j ∈ B₂ := by
    rw [← mem_upEmb B₁ j, ← mem_upEmb B₂ j]
    rw [hEq]
  exact hiff

/-- `upIns` is injective on subsets. -/
lemma upIns_injective_on {k : ℕ} :
    Set.InjOn (upIns : Finset (Fin k) → Finset (Fin (k + 1)))
      ((Finset.univ : Finset (Fin k)).powerset : Set (Finset (Fin k))) := by
  classical
  intro B₁ hB₁ B₂ hB₂ hEq
  have her : (upIns B₁).erase last = (upIns B₂).erase last := by rw [hEq]
  have h1 : (upIns B₁).erase last = upEmb B₁ := by
    ext j
    by_cases hjlast : j = last
    · subst hjlast
      simp [upIns, last_not_mem_upEmb B₁]
    · simp [upIns, Finset.mem_erase, hjlast]
  have h2 : (upIns B₂).erase last = upEmb B₂ := by
    ext j
    by_cases hjlast : j = last
    · subst hjlast
      simp [upIns, last_not_mem_upEmb B₂]
    · simp [upIns, Finset.mem_erase, hjlast]
  have hup : upEmb B₁ = upEmb B₂ := by
    rw [← h1, ← h2]
    exact her
  ext j
  have hiff : j ∈ B₁ ↔ j ∈ B₂ := by
    rw [← mem_upEmb B₁ j, ← mem_upEmb B₂ j]
    rw [hup]
  exact hiff

/-- One-step recursion of the averaged function (eq. (eq: aux averaging)). -/
lemma avgF_rec {f : ℤ → ℝ} {p : unitInterval} (k : ℕ) (x : Fin (k + 1) → ℤ)
    (t : ℤ) :
    avgF f p (k + 1) x t =
      (1 - (p : ℝ)) * avgF f p k (pre x k (Nat.le_succ k)) t +
        (p : ℝ) * avgF f p k (pre x k (Nat.le_succ k)) (t + x last) := by
  classical
  let P : Finset (Finset (Fin (k + 1))) :=
    (Finset.univ : Finset (Fin (k + 1))).powerset
  let g : Finset (Fin (k + 1)) → ℝ := fun B =>
    wB (k + 1) p B * f (t + subSum x B)
  -- partition P into the last-free and last-containing parts
  have hpart : (∑ B ∈ P, g B) =
      (∑ B ∈ P.filter (fun B : Finset (Fin (k + 1)) => last ∈ B), g B)
        + (∑ B ∈ P.filter (fun B : Finset (Fin (k + 1)) => last ∉ B), g B) := by
    calc
      (∑ B ∈ P, g B)
          = (∑ B ∈ P, (if last ∈ B then g B else 0)) + (∑ B ∈ P, (if last ∉ B then g B else 0)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro B hB
            by_cases h : last ∈ B <;> simp [h]
      _ = (∑ B ∈ P.filter (fun B : Finset (Fin (k + 1)) => last ∈ B), g B)
            + ∑ B ∈ P.filter (fun B : Finset (Fin (k + 1)) => last ∉ B), g B := by
            rw [← Finset.sum_filter (s := P) (p := fun B : Finset (Fin (k + 1)) => last ∈ B) (f := g)]
            rw [← Finset.sum_filter (s := P) (p := fun B : Finset (Fin (k + 1)) => last ∉ B) (f := g)]
  -- A0-part equals (1−p)·(inner average at t)
  have hA0 : (∑ B ∈ P.filter (fun B : Finset (Fin (k + 1)) => last ∉ B), g B) =
      (1 - (p : ℝ)) * (∑ B' ∈ (Finset.univ : Finset (Fin k)).powerset,
        wB k p B' * f (t + subSum (pre x k (Nat.le_succ k)) B')) := by
    rw [hA0_eq, Finset.sum_image (f := g) (s := (Finset.univ : Finset (Fin k)).powerset)
      (g := (upEmb : Finset (Fin k) → Finset (Fin (k + 1)))) (upEmb_injective_on (k := k))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B' hB'
    calc
      g (upEmb B') = wB (k + 1) p (upEmb B') * f (t + subSum x (upEmb B')) := by rfl
      _ = ((1 - (p : ℝ)) * wB k p B') * f (t + subSum (pre x k (Nat.le_succ k)) B') := by
            rw [wB_upEmb p B', subSum_upEmb (ℓ := k) x B']
      _ = (1 - (p : ℝ)) * (wB k p B' * f (t + subSum (pre x k (Nat.le_succ k)) B')) := by ring
  -- A1-part equals p·(inner average at t + x last)
  have hA1 : (∑ B ∈ P.filter (fun B : Finset (Fin (k + 1)) => last ∈ B), g B) =
      (p : ℝ) * (∑ B' ∈ (Finset.univ : Finset (Fin k)).powerset,
        wB k p B' * f (t + x last + subSum (pre x k (Nat.le_succ k)) B')) := by
    rw [hA1_eq, Finset.sum_image (f := g) (s := (Finset.univ : Finset (Fin k)).powerset)
      (g := (upIns : Finset (Fin k) → Finset (Fin (k + 1)))) (upIns_injective_on (k := k))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B' hB'
    calc
      g (upIns B') = wB (k + 1) p (upIns B') * f (t + subSum x (upIns B')) := by rfl
      _ = ((p : ℝ) * wB k p B') * f (t + (subSum (pre x k (Nat.le_succ k)) B' + x last)) := by
            rw [wB_upIns p B', subSum_upIns (ℓ := k) x B']
      _ = (p : ℝ) * (wB k p B' * f (t + x last + subSum (pre x k (Nat.le_succ k)) B')) := by
            have harg : t + (subSum (pre x k (Nat.le_succ k)) B' + x last) =
                t + x last + subSum (pre x k (Nat.le_succ k)) B' := by omega
            rw [harg]
            ring
  calc
    avgF f p (k + 1) x t = ∑ B ∈ P, g B := by rfl
    _ = (∑ B ∈ P.filter (fun B => last ∉ B), g B) + ∑ B ∈ P.filter (fun B => last ∈ B), g B := by
          rw [hpart, add_comm]
    _ = (1 - (p : ℝ)) * (∑ B' ∈ (Finset.univ : Finset (Fin k)).powerset,
          wB k p B' * f (t + subSum (pre x k (Nat.le_succ k)) B'))
        + (p : ℝ) * (∑ B' ∈ (Finset.univ : Finset (Fin k)).powerset,
          wB k p B' * f (t + x last + subSum (pre x k (Nat.le_succ k)) B')) := by
          rw [hA0, hA1]
    _ = (1 - (p : ℝ)) * avgF f p k (pre x k (Nat.le_succ k)) t
        + (p : ℝ) * avgF f p k (pre x k (Nat.le_succ k)) (t + x last) := by
          rfl



/-! ## Supremum of a nonnegative summable function on ℤ -/

/-- The supremum `‖f‖∞` of `f : ℤ → ℝ`. -/
noncomputable def esup (f : ℤ → ℝ) : ℝ := sSup (Set.range f)

/-- A point value never exceeds the total mass of a nonnegative summable
function. -/
lemma f_le_norm₁ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
    (t : ℤ) : f t ≤ norm₁ f := by
  have hsingle : f t ≤ ∑ s ∈ ({t} : Finset ℤ), f s := by
    simp
  exact le_trans hsingle (Finset_sum_le_norm₁ hfpos hfsum ({t} : Finset ℤ))

/-- The range of a nonnegative summable function is bounded above by its total
mass. -/
lemma bddAbove_range_norm₁ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t)
    (hfsum : Summable f) : BddAbove (Set.range f) := by
  refine ⟨norm₁ f, ?_⟩
  intro y hy
  rcases hy with ⟨t, rfl⟩
  exact f_le_norm₁ hfpos hfsum t

/-- Every point value is below the supremum. -/
lemma le_esup {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
    (t : ℤ) : f t ≤ esup f := by
  dsimp [esup]
  exact le_csSup (bddAbove_range_norm₁ hfpos hfsum) ⟨t, rfl⟩

/-- The supremum is at most the total mass. -/
lemma esup_le_norm₁ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f) :
    esup f ≤ norm₁ f := by
  dsimp [esup]
  exact csSup_le (s := Set.range f) (a := norm₁ f) ⟨f 0, ⟨0, rfl⟩⟩ (by
    intro b hb
    rcases hb with ⟨t, rfl⟩
    exact f_le_norm₁ hfpos hfsum t)

/-- The supremum of a nonnegative function is nonnegative. -/
lemma esup_nonneg {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f) :
    0 ≤ esup f := by
  exact le_trans (hfpos 0) (le_esup hfpos hfsum 0)




/-! ## The decay predicate and the shrinkage lemma -/

/-- `t` *decays* with respect to the pre-function `F`, displacement `d`, and
threshold `T`: both shifted values `F(t ± d)` are at most `T`.  In the paper
(Lemma l:aux 09019847294), `F = f_{A,p,m−1}`, `d = X_m` and
`T = R/(N√n)`; `t` is the point `t_{m−1}` of a descendant sequence. -/
def decaysAt (F : ℤ → ℝ) (d : ℤ) (T : ℝ) (t : ℤ) : Prop :=
  F (t + d) ≤ T ∧ F (t - d) ≤ T

/-- A decaying step shrinks the averaged value by the factor `1 − p + ε/2`
(Lemma l:aux 09019847294): for `post t := (1−p)·F t + p·F (t+d)` — the value
`f_{A,p,m}(t)` obtained by one averaging step from `F := f_{A,p,m−1}` — both
choices `t = u` and `t = u − d` of the backward step give
`post t ≤ (1 − p + ε/2)·F u`, provided `u` decays (`F(u ± d) ≤ T`) and
`T ≤ (ε/(2p))·F u` (which holds when `F u > L/(N√n)` and
`T = εL/(2pN√n)`). -/
lemma shrink_of_decay {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε2p : ε ≤ 2 * (p : ℝ))
    {F : ℤ → ℝ} {u d : ℤ} {T : ℝ} (hdec : decaysAt F d T u)
    (hbig : T ≤ (ε / (2 * (p : ℝ))) * F u) (hFu0 : 0 ≤ F u) :
    (1 - (p : ℝ)) * F u + (p : ℝ) * F (u + d) ≤ (1 - (p : ℝ) + ε / 2) * F u ∧
      (1 - (p : ℝ)) * F (u - d) + (p : ℝ) * F u ≤ (1 - (p : ℝ) + ε / 2) * F u := by
  constructor
  · -- case t = u : coefficient (1−p) on the large value, p on the small one
    have hFud : F (u + d) ≤ (ε / (2 * (p : ℝ))) * F u := le_trans hdec.1 hbig
    have hp0 : 0 ≤ (p : ℝ) := le_of_lt hp₀
    have hcoef : (p : ℝ) * ((ε / (2 * (p : ℝ))) * F u) = (ε / 2) * F u := by
      field_simp [show (p : ℝ) ≠ 0 by positivity]
    calc
      (1 - (p : ℝ)) * F u + (p : ℝ) * F (u + d)
          ≤ (1 - (p : ℝ)) * F u + (p : ℝ) * ((ε / (2 * (p : ℝ))) * F u) := by
            exact add_le_add_right (mul_le_mul_of_nonneg_left hFud hp0) ((1 - (p : ℝ)) * F u)
      _ = (1 - (p : ℝ)) * F u + (ε / 2) * F u := by rw [hcoef]
      _ = (1 - (p : ℝ) + ε / 2) * F u := by ring
  · -- case t = u − d : coefficient p on the large value, (1−p) on the small one
    have hFud' : F (u - d) ≤ (ε / (2 * (p : ℝ))) * F u := le_trans hdec.2 hbig
    have hp1m : 0 ≤ 1 - (p : ℝ) := by linarith [p.property.2]
    have hcoef' : (1 - (p : ℝ)) * ((ε / (2 * (p : ℝ))) * F u) =
        ((1 - (p : ℝ)) * ε / (2 * (p : ℝ))) * F u := by ring
    have hc : (p : ℝ) + (1 - (p : ℝ)) * ε / (2 * (p : ℝ)) ≤ 1 - (p : ℝ) + ε / 2 := by
      have h1 : 0 ≤ 1 - 2 * (p : ℝ) := by nlinarith [hp₁]
      have hd : ε / (2 * (p : ℝ)) ≤ 1 := by
        rw [div_le_iff₀ (by positivity : 0 < 2 * (p : ℝ))]
        simpa using hε2p
      have h2 : 0 ≤ 1 - ε / (2 * (p : ℝ)) := by nlinarith
      have hprod : 0 ≤ (1 - 2 * (p : ℝ)) * (1 - ε / (2 * (p : ℝ))) := mul_nonneg h1 h2
      have hid : 1 - (p : ℝ) + ε / 2 - ((p : ℝ) + (1 - (p : ℝ)) * ε / (2 * (p : ℝ))) =
          (1 - 2 * (p : ℝ)) * (1 - ε / (2 * (p : ℝ))) := by
        field_simp [show (p : ℝ) ≠ 0 by positivity]
        ring
      nlinarith [hprod, hid]
    calc
      (1 - (p : ℝ)) * F (u - d) + (p : ℝ) * F u
          = (p : ℝ) * F u + (1 - (p : ℝ)) * F (u - d) := by ring
      _ ≤ (p : ℝ) * F u + (1 - (p : ℝ)) * ((ε / (2 * (p : ℝ))) * F u) := by
            exact add_le_add_right (mul_le_mul_of_nonneg_left hFud' hp1m) ((p : ℝ) * F u)
      _ = ((p : ℝ) + (1 - (p : ℝ)) * ε / (2 * (p : ℝ))) * F u := by ring
      _ ≤ (1 - (p : ℝ) + ε / 2) * F u := by
            exact mul_le_mul_of_nonneg_right hc hFu0

/-- Averaging preserves nonnegativity. -/
lemma avgF_nonneg {f : ℤ → ℝ} {p : unitInterval} {ℓ : ℕ} {x : Fin ℓ → ℤ}
    (hfpos : ∀ t : ℤ, 0 ≤ f t) (t : ℤ) : 0 ≤ avgF f p ℓ x t := by
  dsimp [avgF]
  exact Finset.sum_nonneg (by
    intro B hB
    exact mul_nonneg (wB_nonneg ℓ p B) (hfpos (t + subSum x B)))

/-- One averaging step never exceeds the larger of the two pre-values
(used to choose the backward step of the descendant sequence). -/
lemma avgF_le_max {f : ℤ → ℝ} {p : unitInterval} (k : ℕ) (x : Fin (k + 1) → ℤ)
    (t : ℤ) :
    avgF f p (k + 1) x t ≤
      max (avgF f p k (pre x k (Nat.le_succ k)) t)
        (avgF f p k (pre x k (Nat.le_succ k)) (t + x last)) := by
  rw [avgF_rec]
  have hp0 : 0 ≤ (p : ℝ) := p.property.1
  have hp1m : 0 ≤ 1 - (p : ℝ) := by linarith [p.property.2]
  have hA : (1 - (p : ℝ)) * avgF f p k (pre x k (Nat.le_succ k)) t ≤
      (1 - (p : ℝ)) * max (avgF f p k (pre x k (Nat.le_succ k)) t)
        (avgF f p k (pre x k (Nat.le_succ k)) (t + x last)) := by
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hp1m
  have hB : (p : ℝ) * avgF f p k (pre x k (Nat.le_succ k)) (t + x last) ≤
      (p : ℝ) * max (avgF f p k (pre x k (Nat.le_succ k)) t)
        (avgF f p k (pre x k (Nat.le_succ k)) (t + x last)) := by
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hp0
  calc
    (1 - (p : ℝ)) * avgF f p k (pre x k (Nat.le_succ k)) t +
        (p : ℝ) * avgF f p k (pre x k (Nat.le_succ k)) (t + x last)
        ≤ (1 - (p : ℝ)) * max (avgF f p k (pre x k (Nat.le_succ k)) t)
            (avgF f p k (pre x k (Nat.le_succ k)) (t + x last))
          + (p : ℝ) * max (avgF f p k (pre x k (Nat.le_succ k)) t)
            (avgF f p k (pre x k (Nat.le_succ k)) (t + x last)) := add_le_add hA hB
    _ = max (avgF f p k (pre x k (Nat.le_succ k)) t)
            (avgF f p k (pre x k (Nat.le_succ k)) (t + x last)) := by ring




/-! ## Level functions and the backward descent step -/

/-- The level-`m` averaged function `f_{A,p,m}` over the first `m` coordinates
of `x` (as a function on `ℤ`). -/
def flvl {ℓ : ℕ} (f : ℤ → ℝ) (p : unitInterval) (x : Fin ℓ → ℤ)
    (m : ℕ) (hm : m ≤ ℓ) : ℤ → ℝ :=
  fun t => avgF f p m (pre x m hm) t

/-- Restricting to the first `m+1` and then the first `m` coordinates is the
same as restricting to the first `m` directly. -/
lemma pre_pre_eq {ℓ : ℕ} (x : Fin ℓ → ℤ) {m : ℕ} (hm : m < ℓ) :
    pre (pre x (m + 1) (Nat.succ_le_of_lt hm)) m (Nat.le_succ m) =
      pre x m (le_of_lt hm) := by
  funext j
  dsimp [pre]
  congr 1

/-- The `last` coordinate of the first `m+1` coordinates of `x` is `x ⟨m⟩`. -/
lemma pre_last_eq {ℓ : ℕ} (x : Fin ℓ → ℤ) {m : ℕ} (hm : m < ℓ) :
    pre x (m + 1) (Nat.succ_le_of_lt hm) last = x ⟨m, hm⟩ := by
  simp [pre, last]

/-- Leveled one-step recursion: `f_{A,p,m+1}(t) = (1−p)·f_{A,p,m}(t) +
p·f_{A,p,m}(t + xₘ)`. -/
lemma flvl_rec {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {m : ℕ} (hm : m < ℓ) (t : ℤ) :
    flvl f p x (m + 1) (Nat.succ_le_of_lt hm) t =
      (1 - (p : ℝ)) * flvl f p x m (le_of_lt hm) t +
        (p : ℝ) * flvl f p x m (le_of_lt hm) (t + x ⟨m, hm⟩) := by
  have hrec := avgF_rec (f := f) (p := p) m (pre x (m + 1) (Nat.succ_le_of_lt hm)) t
  -- hrec gives the recursion for the (m+1)-prefix; pull back to x
  have hpre := pre_pre_eq (ℓ := ℓ) x hm
  have hlst := pre_last_eq (ℓ := ℓ) x hm
  -- rewrite the RHS of hrec into flvl terms
  have h1 : pre (pre x (m + 1) (Nat.succ_le_of_lt hm)) m (Nat.le_succ m) =
      pre x m (le_of_lt hm) := hpre
  have h2 : (pre x (m + 1) (Nat.succ_le_of_lt hm)) last = x ⟨m, hm⟩ := hlst
  calc
    flvl f p x (m + 1) (Nat.succ_le_of_lt hm) t
        = avgF f p (m + 1) (pre x (m + 1) (Nat.succ_le_of_lt hm)) t := rfl
    _ = (1 - (p : ℝ)) * avgF f p m
            (pre (pre x (m + 1) (Nat.succ_le_of_lt hm)) m (Nat.le_succ m)) t
          + (p : ℝ) * avgF f p m
            (pre (pre x (m + 1) (Nat.succ_le_of_lt hm)) m (Nat.le_succ m))
            (t + (pre x (m + 1) (Nat.succ_le_of_lt hm)) last) := hrec
    _ = (1 - (p : ℝ)) * flvl f p x m (le_of_lt hm) t
          + (p : ℝ) * flvl f p x m (le_of_lt hm) (t + x ⟨m, hm⟩) := by
          rw [h1, h2]
          rfl

/-- Backward descent step: from a point `t_up` at level `m+1` one can move to
a point at level `m` (`t_up`, or `t_up + xₘ`) whose level-`m` value is at
least the level-`(m+1)` value.  This is the choice `v = 0` vs `v = 1` of the
descendant-sequence construction. -/
lemma descent_step {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {m : ℕ} (hm : m < ℓ) (t_up : ℤ) :
    ∃ v : Bool, flvl f p x m (le_of_lt hm) (t_up + (if v then x ⟨m, hm⟩ else 0)) ≥
      flvl f p x (m + 1) (Nat.succ_le_of_lt hm) t_up := by
  let A : ℝ := flvl f p x m (le_of_lt hm) t_up
  let B : ℝ := flvl f p x m (le_of_lt hm) (t_up + x ⟨m, hm⟩)
  let V : ℝ := flvl f p x (m + 1) (Nat.succ_le_of_lt hm) t_up
  have hmax : V ≤ max A B := by
    dsimp [A, B, V]
    rw [flvl_rec hm t_up]
    have hp0 : 0 ≤ (p : ℝ) := p.property.1
    have hp1m : 0 ≤ 1 - (p : ℝ) := by linarith [p.property.2]
    calc
      (1 - (p : ℝ)) * flvl f p x m (le_of_lt hm) t_up +
          (p : ℝ) * flvl f p x m (le_of_lt hm) (t_up + x ⟨m, hm⟩)
          ≤ (1 - (p : ℝ)) * max (flvl f p x m (le_of_lt hm) t_up)
              (flvl f p x m (le_of_lt hm) (t_up + x ⟨m, hm⟩))
            + (p : ℝ) * max (flvl f p x m (le_of_lt hm) t_up)
              (flvl f p x m (le_of_lt hm) (t_up + x ⟨m, hm⟩)) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (le_max_left _ _) hp1m)
              (mul_le_mul_of_nonneg_left (le_max_right _ _) hp0)
      _ = max (flvl f p x m (le_of_lt hm) t_up)
              (flvl f p x m (le_of_lt hm) (t_up + x ⟨m, hm⟩)) := by ring
  by_cases hA : A ≥ V
  · refine ⟨false, ?_⟩
    dsimp [A, V]
    simpa using hA
  · refine ⟨true, ?_⟩
    dsimp [A, B, V]
    have hlt : flvl f p x m (le_of_lt hm) t_up < V := lt_of_not_ge hA
    by_contra hB
    have hB' : flvl f p x m (le_of_lt hm) (t_up + x ⟨m, hm⟩) < V := lt_of_not_ge hB
    have hboth : max (flvl f p x m (le_of_lt hm) t_up)
        (flvl f p x m (le_of_lt hm) (t_up + x ⟨m, hm⟩)) < V := max_lt hlt hB'
    exact (not_lt_of_ge hmax) hboth







/-- Restricting to `ℓ`, then to `m ≤ ℓ`, is restricting to `m` directly
(the prefix-composition identity). -/
lemma pre_pre_gen {ℓ : ℕ} (x : Fin (ℓ + 1) → ℤ) {m : ℕ} (hm : m ≤ ℓ) :
    pre (pre x ℓ (Nat.le_succ ℓ)) m hm = pre x m (Nat.le_trans hm (Nat.le_succ ℓ)) := by
  funext j
  dsimp [pre]
  congr 1

/-- The level function does not depend on the proof that `m ≤ ℓ`. -/
lemma flvl_hm_irrel {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {m : ℕ} {h₁ h₂ : m ≤ ℓ} : flvl f p x m h₁ = flvl f p x m h₂ := by
  funext t
  dsimp [flvl]




/-! ## The backward chain (walk from the top level down to level 0) -/

/-- The prefix-restriction does not depend on the bound proof. -/
lemma pre_hm_irrel {ℓ : ℕ} (x : Fin ℓ → ℤ) {m : ℕ} {p₁ p₂ : m ≤ ℓ} :
    pre x m p₁ = pre x m p₂ := by
  funext j
  dsimp [pre]

/-- A backward walk from the top point `t_top`, indexed by natural levels:
`t m hm` is the point at level `m ≤ ℓ`.  The level-`(m+1)` value never
exceeds the level-`m` value, and the level-`m` point arises from the
level-`(m+1)` point by adding `0` or `x ⟨m, ·⟩`. -/
structure BWalk {ℓ : ℕ} (f : ℤ → ℝ) (p : unitInterval) (x : Fin ℓ → ℤ)
    (t_top : ℤ) where
  t : (m : ℕ) → m ≤ ℓ → ℤ
  t_irrel : ∀ {m : ℕ} {p₁ p₂ : m ≤ ℓ}, t m p₁ = t m p₂
  htop : t ℓ (Nat.le_refl ℓ) = t_top
  hmono : ∀ (m : ℕ) (hm1 : m + 1 ≤ ℓ),
    flvl f p x (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1))
      (t (m + 1) hm1) ≤
    flvl f p x m (Nat.le_trans (Nat.le_succ m) hm1)
      (t m (Nat.le_trans (Nat.le_succ m) hm1))
  hrel : ∀ (m : ℕ) (hm1 : m + 1 ≤ ℓ),
    (t m (Nat.le_trans (Nat.le_succ m) hm1) =
        t (m + 1) hm1 + x ⟨m, Nat.lt_of_succ_le hm1⟩) ∨
    (t m (Nat.le_trans (Nat.le_succ m) hm1) = t (m + 1) hm1)

/-- The base walk at length 0. -/
def baseWalk {f : ℤ → ℝ} {p : unitInterval} (x : Fin 0 → ℤ) (t_top : ℤ) :
    BWalk f p x t_top := by
  refine ⟨fun m hm => t_top, ?_, ?_, ?_, ?_⟩
  · intro m p₁ p₂
    rfl
  · rfl
  · intro m hm1
    exact False.elim ((Nat.not_succ_le_zero m) hm1)
  · intro m hm1
    exact False.elim ((Nat.not_succ_le_zero m) hm1)

/-- Extend a walk on the first `ℓ` coordinates by one top step: `h₀` says the
level-`ℓ` value at `t_k` is at least the level-`(ℓ+1)` value at `t_top`, and
`hrelTop` records how `t_k` relates to `t_top`. -/
noncomputable def extendWalk {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} (x : Fin (ℓ + 1) → ℤ)
    (t_top : ℤ) (t_k : ℤ) (W' : BWalk f p (pre x ℓ (Nat.le_succ ℓ)) t_k)
    (h₀ : flvl f p x (ℓ + 1) (Nat.le_refl (ℓ + 1)) t_top ≤
      flvl f p x ℓ (Nat.le_succ ℓ) t_k)
    (hrelTop : t_k = t_top + x ⟨ℓ, Nat.lt_succ_self ℓ⟩ ∨ t_k = t_top) :
    BWalk f p x t_top := by
  classical
  let t : (m : ℕ) → m ≤ ℓ + 1 → ℤ := fun m hm =>
    if h : m ≤ ℓ then W'.t m h else t_top
  have tval_lt : ∀ (m : ℕ) (hm : m ≤ ℓ) (hm' : m ≤ ℓ + 1),
      t m hm' = W'.t m hm := by
    intro m hm hm'
    dsimp [t]
    rw [dif_pos hm]
  have tval_top : ∀ (m : ℕ) (hm' : m ≤ ℓ + 1), ¬ m ≤ ℓ → t m hm' = t_top := by
    intro m hm' hnot
    dsimp [t]
    rw [dif_neg hnot]
  have htop : t (ℓ + 1) (Nat.le_refl (ℓ + 1)) = t_top := by
    exact tval_top (ℓ + 1) (Nat.le_refl (ℓ + 1)) (by omega)
  have hmono : ∀ (m : ℕ) (hm1 : m + 1 ≤ ℓ + 1),
      flvl f p x (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1))
        (t (m + 1) hm1) ≤
      flvl f p x m (Nat.le_trans (Nat.le_succ m) hm1)
        (t m (Nat.le_trans (Nat.le_succ m) hm1)) := by
    intro m hm1
    by_cases hle : m + 1 ≤ ℓ
    · have hm_le_ℓ : m ≤ ℓ := Nat.le_trans (Nat.le_succ m) hle
      have htv1 : t (m + 1) hm1 = W'.t (m + 1) hle := tval_lt (m + 1) hle hm1
      have htv0 : t m (Nat.le_trans (Nat.le_succ m) hm1) = W'.t m hm_le_ℓ :=
        tval_lt m hm_le_ℓ (Nat.le_trans (Nat.le_succ m) hm1)
      have hW := W'.hmono m hle
      have hW' : flvl f p x (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1))
            (W'.t (m + 1) hle) ≤
          flvl f p x m (Nat.le_trans (Nat.le_succ m) hm1)
            (W'.t m hm_le_ℓ) := by
        have hc1 : pre (pre x ℓ (Nat.le_succ ℓ)) (m + 1) hle =
            pre x (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1)) := by
          calc
            pre (pre x ℓ (Nat.le_succ ℓ)) (m + 1) hle
                = pre x (m + 1) (Nat.le_trans hle (Nat.le_succ ℓ)) := pre_pre_gen x hle
            _ = pre x (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1)) := pre_hm_irrel x
        have hc2 : pre (pre x ℓ (Nat.le_succ ℓ)) m hm_le_ℓ =
            pre x m (Nat.le_trans (Nat.le_succ m) hm1) := by
          calc
            pre (pre x ℓ (Nat.le_succ ℓ)) m hm_le_ℓ
                = pre x m (Nat.le_trans hm_le_ℓ (Nat.le_succ ℓ)) := pre_pre_gen x hm_le_ℓ
            _ = pre x m (Nat.le_trans (Nat.le_succ m) hm1) := pre_hm_irrel x
        have hW0 : flvl f p (pre x ℓ (Nat.le_succ ℓ)) (m + 1) hle
              (W'.t (m + 1) hle) ≤
            flvl f p (pre x ℓ (Nat.le_succ ℓ)) m hm_le_ℓ
              (W'.t m hm_le_ℓ) := by
          simpa using hW
        dsimp [flvl] at hW0 ⊢
        rw [hc1, hc2] at hW0
        simpa using hW0
      calc
        flvl f p x (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1)) (t (m + 1) hm1)
            = flvl f p x (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1)) (W'.t (m + 1) hle) := by rw [htv1]
        _ ≤ flvl f p x m (Nat.le_trans (Nat.le_succ m) hm1) (W'.t m hm_le_ℓ) := hW'
        _ = flvl f p x m (Nat.le_trans (Nat.le_succ m) hm1) (t m (Nat.le_trans (Nat.le_succ m) hm1)) := by rw [htv0]
    · -- top step: m = ℓ
      have hm_eq : m = ℓ := by omega
      subst m
      have htopv : t (ℓ + 1) hm1 = t_top := tval_top (ℓ + 1) hm1 (by omega)
      have hlv : t ℓ (Nat.le_trans (Nat.le_succ ℓ) hm1) = t_k := by
        have hvv : t ℓ (Nat.le_trans (Nat.le_succ ℓ) hm1) = W'.t ℓ (Nat.le_refl ℓ) :=
          tval_lt ℓ (Nat.le_refl ℓ) (Nat.le_trans (Nat.le_succ ℓ) hm1)
        rw [hvv]
        exact W'.htop
      calc
        flvl f p x (ℓ + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1)) (t (ℓ + 1) hm1)
            = flvl f p x (ℓ + 1) (Nat.le_refl (ℓ + 1)) t_top := by
              rw [htopv]
        _ ≤ flvl f p x ℓ (Nat.le_succ ℓ) t_k := h₀
        _ = flvl f p x ℓ (Nat.le_trans (Nat.le_succ ℓ) hm1) (t ℓ (Nat.le_trans (Nat.le_succ ℓ) hm1)) := by
              rw [hlv]
  have hrel : ∀ (m : ℕ) (hm1 : m + 1 ≤ ℓ + 1),
      (t m (Nat.le_trans (Nat.le_succ m) hm1) =
          t (m + 1) hm1 + x ⟨m, Nat.lt_of_succ_le hm1⟩) ∨
      (t m (Nat.le_trans (Nat.le_succ m) hm1) = t (m + 1) hm1) := by
    intro m hm1
    by_cases hle : m + 1 ≤ ℓ
    · have hm_le_ℓ : m ≤ ℓ := Nat.le_trans (Nat.le_succ m) hle
      have htv1 : t (m + 1) hm1 = W'.t (m + 1) hle := tval_lt (m + 1) hle hm1
      have htv0 : t m (Nat.le_trans (Nat.le_succ m) hm1) = W'.t m hm_le_ℓ :=
        tval_lt m hm_le_ℓ (Nat.le_trans (Nat.le_succ m) hm1)
      have hcoord : (pre x ℓ (Nat.le_succ ℓ)) ⟨m, Nat.lt_of_succ_le hle⟩ =
          x ⟨m, Nat.lt_of_succ_le hm1⟩ := by
        dsimp [pre]
      rcases W'.hrel m hle with hl | hr
      · left
        rw [htv0, htv1]
        simpa [hcoord] using hl
      · right
        rw [htv0, htv1]
        simpa using hr
    · -- top step: m = ℓ
      have hm_eq : m = ℓ := by omega
      subst m
      have htopv : t (ℓ + 1) hm1 = t_top := tval_top (ℓ + 1) hm1 (by omega)
      have hlv : t ℓ (Nat.le_trans (Nat.le_succ ℓ) hm1) = t_k := by
        have hvv : t ℓ (Nat.le_trans (Nat.le_succ ℓ) hm1) = W'.t ℓ (Nat.le_refl ℓ) :=
          tval_lt ℓ (Nat.le_refl ℓ) (Nat.le_trans (Nat.le_succ ℓ) hm1)
        rw [hvv]
        exact W'.htop
      rw [htopv, hlv]
      rcases hrelTop with hl | hr
      · left
        simpa using hl
      · right
        simpa using hr
  exact ⟨t, (by intro m p₁ p₂; dsimp [t]), htop, hmono, hrel⟩

/-- Construct the backward walk from the top point `t_top` (length recursion):
for every `m ≤ ℓ` the value at level `m` is at least the value at the top
level `ℓ`, and consecutive points differ by `0` or `x ⟨m, ·⟩`. -/
noncomputable def backward_chain (f : ℤ → ℝ) (p : unitInterval) :
    ∀ {ℓ : ℕ} (x : Fin ℓ → ℤ) (t_top : ℤ), BWalk f p x t_top
  | 0, x, t_top => baseWalk x t_top
  | ℓ + 1, x, t_top =>
      by
        classical
        let hstep := descent_step (f := f) (p := p) (ℓ := ℓ + 1) (x := x) (m := ℓ) (Nat.lt_succ_self ℓ) t_top
        let v₀ : Bool := Classical.choose hstep
        have hv₀ := Classical.choose_spec hstep
        let t_k : ℤ := t_top + (if v₀ then x ⟨ℓ, Nat.lt_succ_self ℓ⟩ else 0)
        have h₀ : flvl f p x (ℓ + 1) (Nat.le_refl (ℓ + 1)) t_top ≤
            flvl f p x ℓ (Nat.le_succ ℓ) t_k := by
          simpa [t_k] using hv₀
        have hrelTop : t_k = t_top + x ⟨ℓ, Nat.lt_succ_self ℓ⟩ ∨ t_k = t_top := by
          by_cases hv : v₀
          · left
            dsimp [t_k]
            simp [hv]
          · right
            dsimp [t_k]
            simp [hv]
        have W' : BWalk f p (pre x ℓ (Nat.le_succ ℓ)) t_k :=
          backward_chain f p (pre x ℓ (Nat.le_succ ℓ)) t_k
        exact extendWalk x t_top t_k W' h₀ hrelTop



/-- Decay of the level-`m` point of a walk (decay at time `m+1`). -/
def levelDecays {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) (m : ℕ) (hm1 : m + 1 ≤ ℓ) : Prop :=
  decaysAt (flvl f p x m (Nat.le_trans (Nat.le_succ m) hm1))
    (x ⟨m, Nat.lt_of_succ_le hm1⟩) T
    (W.t m (Nat.le_trans (Nat.le_succ m) hm1))

/-- Number of decaying levels among `0..m−1` (definitional successor case). -/
noncomputable def decayUpTo {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) :
    (m : ℕ) → m ≤ ℓ → ℕ
  | 0, _ => 0
  | m + 1, hm1 => by
      classical
      exact decayUpTo W T m (Nat.le_trans (Nat.le_succ m) hm1) +
        (if levelDecays W T m hm1 then 1 else 0)

lemma decayUpTo_zero {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) :
    decayUpTo W T 0 (Nat.zero_le ℓ) = 0 := by
  rfl

/-- A decaying level shrinks the chain value by `b := 1 − p + ε/2`. -/
lemma level_shrink {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ)
    {m : ℕ} (hm1 : m + 1 ≤ ℓ) {ε : ℝ} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    (hε2p : ε ≤ 2 * (p : ℝ))
    (hbig : T ≤ (ε / (2 * (p : ℝ))) *
      flvl f p x m (Nat.le_trans (Nat.le_succ m) hm1)
        (W.t m (Nat.le_trans (Nat.le_succ m) hm1)))
    (hfpos : ∀ t : ℤ, 0 ≤ f t)
    (hdec : levelDecays W T m hm1) :
    flvl f p x (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1))
        (W.t (m + 1) hm1) ≤
      (1 - (p : ℝ) + ε / 2) *
        flvl f p x m (Nat.le_trans (Nat.le_succ m) hm1)
          (W.t m (Nat.le_trans (Nat.le_succ m) hm1)) := by
  classical
  let d : ℤ := x ⟨m, Nat.lt_of_succ_le hm1⟩
  let F : ℤ → ℝ := flvl f p x m (Nat.le_trans (Nat.le_succ m) hm1)
  let u : ℤ := W.t m (Nat.le_trans (Nat.le_succ m) hm1)
  have hFu0 : 0 ≤ F u := by
    dsimp [F, u, flvl]
    exact avgF_nonneg (f := f) (p := p) (ℓ := m)
      (x := pre x m (Nat.le_trans (Nat.le_succ m) hm1)) hfpos
      (W.t m (Nat.le_trans (Nat.le_succ m) hm1))
  have hdec' : decaysAt F d T u := by simpa [levelDecays, F, u, d] using hdec
  -- hrec with canonical proof args
  have hrec := flvl_rec (f := f) (p := p) (x := x) (hm := Nat.lt_of_succ_le hm1)
    (W.t (m + 1) hm1)
  have hrec' : flvl f p x (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1))
        (W.t (m + 1) hm1) =
      (1 - (p : ℝ)) * F (W.t (m + 1) hm1) + (p : ℝ) * F (W.t (m + 1) hm1 + d) := by
    dsimp [F, d]
    -- convert hrec's m-level proof arg to the canonical one
    have hlevel : flvl f p x m (Nat.le_of_lt (Nat.lt_of_succ_le hm1)) =
        flvl f p x m (Nat.le_trans (Nat.le_succ m) hm1) := flvl_hm_irrel
    rw [hlevel] at hrec
    exact hrec
  rcases W.hrel m hm1 with hl | hr
  · -- case A: u = W.t (m+1) + d
    have hu : W.t (m + 1) hm1 = u - d := by
      dsimp [u, d] at hl ⊢
      omega
    have hsh := (shrink_of_decay hp₀ hp₁ hε2p hdec' hbig hFu0).2
    -- hsh : (1−p)·F(u−d) + p·F(u) ≤ b·F(u)
    calc
      flvl f p x (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1)) (W.t (m + 1) hm1)
          = (1 - (p : ℝ)) * F (W.t (m + 1) hm1) + (p : ℝ) * F (W.t (m + 1) hm1 + d) := hrec'
      _ = (1 - (p : ℝ)) * F (u - d) + (p : ℝ) * F (u - d + d) := by
            rw [hu]
      _ = (1 - (p : ℝ)) * F (u - d) + (p : ℝ) * F u := by
            rw [show u - d + d = u by omega]
      _ ≤ (1 - (p : ℝ) + ε / 2) * F u := hsh
      _ = (1 - (p : ℝ) + ε / 2) *
            flvl f p x m (Nat.le_trans (Nat.le_succ m) hm1)
              (W.t m (Nat.le_trans (Nat.le_succ m) hm1)) := rfl
  · -- case B: u = W.t (m+1)
    have hu : W.t (m + 1) hm1 = u := by
      dsimp [u]
      omega
    have hsh := (shrink_of_decay hp₀ hp₁ hε2p hdec' hbig hFu0).1
    calc
      flvl f p x (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1)) (W.t (m + 1) hm1)
          = (1 - (p : ℝ)) * F (W.t (m + 1) hm1) + (p : ℝ) * F (W.t (m + 1) hm1 + d) := hrec'
      _ = (1 - (p : ℝ)) * F u + (p : ℝ) * F (u + d) := by
            rw [hu]
      _ ≤ (1 - (p : ℝ) + ε / 2) * F u := hsh
      _ = (1 - (p : ℝ) + ε / 2) *
            flvl f p x m (Nat.le_trans (Nat.le_succ m) hm1)
              (W.t m (Nat.le_trans (Nat.le_succ m) hm1)) := rfl

/-- Along the walk, the top value is at most `b` to the power of the number of
decaying levels times the level-0 value, `b := 1 − p + ε/2`. -/
lemma chain_value_bound {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    (hε2p : ε ≤ 2 * (p : ℝ))
    (hfpos : ∀ t : ℤ, 0 ≤ f t)
    (hbig : ∀ (m : ℕ) (hm : m ≤ ℓ),
      T ≤ (ε / (2 * (p : ℝ))) * flvl f p x m hm (W.t m hm)) :
    flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) ≤
      (1 - (p : ℝ) + ε / 2) ^ decayUpTo W T ℓ (Nat.le_refl ℓ) *
        flvl f p x 0 (Nat.zero_le ℓ) (W.t 0 (Nat.zero_le ℓ)) := by
  classical
  let b : ℝ := 1 - (p : ℝ) + ε / 2
  let V0 : ℝ := flvl f p x 0 (Nat.zero_le ℓ) (W.t 0 (Nat.zero_le ℓ))
  have hb0 : 0 ≤ b := by
    dsimp [b]
    have h1 : 0 ≤ 1 - (p : ℝ) := by linarith [p.property.2]
    nlinarith
  have main : ∀ (m : ℕ) (hm : m ≤ ℓ),
      flvl f p x m hm (W.t m hm) ≤ b ^ decayUpTo W T m hm * V0 := by
    intro m
    induction m with
    | zero =>
        intro hm
        have hd : decayUpTo W T 0 hm = 0 := rfl
        dsimp [V0]
        rw [hd, pow_zero]
        -- flvl 0 hm = flvl 0 (zero_le ℓ); W.t 0 hm = W.t 0 (zero_le ℓ)
        have hf : flvl f p x 0 hm (W.t 0 hm) = flvl f p x 0 (Nat.zero_le ℓ) (W.t 0 (Nat.zero_le ℓ)) := by
          rw [flvl_hm_irrel]
          congr 1
        simpa [hf]
    | succ m ih =>
        intro hm1
        have hmle : m ≤ ℓ := Nat.le_trans (Nat.le_succ m) hm1
        have ih' := ih hmle
        by_cases hdec : levelDecays W T m hm1
        · -- decaying level: shrink then multiply
          have hsh := level_shrink W T hm1 hp₀ hp₁ hε2p
            (hbig m hmle) hfpos hdec
          have hc : decayUpTo W T (m + 1) hm1 = decayUpTo W T m hmle + 1 := by
            dsimp [decayUpTo]
            simp [hdec]
          calc
            flvl f p x (m + 1) hm1 (W.t (m + 1) hm1)
                = flvl f p x (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1))
                    (W.t (m + 1) hm1) := by
                    rw [show flvl f p x (m + 1) hm1 =
                        flvl f p x (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1)) by
                          exact flvl_hm_irrel]
            _ ≤ b * flvl f p x m hmle (W.t m hmle) := by
                  dsimp [b]
                  simpa using hsh
            _ ≤ b * (b ^ decayUpTo W T m hmle * V0) := by
                  exact mul_le_mul_of_nonneg_left ih' hb0
            _ = b ^ (decayUpTo W T m hmle + 1) * V0 := by
                  rw [pow_succ']
                  ring
            _ = b ^ decayUpTo W T (m + 1) hm1 * V0 := by rw [hc]
        · -- non-decaying level: hmono
          have hmono' : flvl f p x (m + 1) hm1 (W.t (m + 1) hm1) ≤
              flvl f p x m hmle (W.t m hmle) := by
            have hm0 := W.hmono m hm1
            rw [show flvl f p x (m + 1) hm1 =
                flvl f p x (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1)) by
                  exact flvl_hm_irrel]
            simpa using hm0
          have hc : decayUpTo W T (m + 1) hm1 = decayUpTo W T m hmle := by
            dsimp [decayUpTo]
            simp [hdec]
          calc
            flvl f p x (m + 1) hm1 (W.t (m + 1) hm1)
                ≤ flvl f p x m hmle (W.t m hmle) := hmono'
            _ ≤ b ^ decayUpTo W T m hmle * V0 := ih'
            _ = b ^ decayUpTo W T (m + 1) hm1 * V0 := by rw [hc]
  have htop : flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) ≤
      b ^ decayUpTo W T ℓ (Nat.le_refl ℓ) * V0 := main ℓ (Nat.le_refl ℓ)
  simpa [b, V0] using htop



/-- The level-0 function is `f` itself. -/
lemma flvl_zero {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ} (t : ℤ) :
    flvl f p x 0 (Nat.zero_le ℓ) t = f t := by
  classical
  dsimp [flvl, avgF]
  -- only the empty subset contributes
  have hsub : (Finset.univ : Finset (Fin 0)).powerset = ({∅} : Finset (Finset (Fin 0))) := by
    ext B
    simp [Finset.mem_powerset]
  rw [hsub]
  simp [wB, subSum]


/-- Level values never drop below the top value: `flvl ℓ (W.t ℓ) ≤ flvl m (W.t m)`
for every `m ≤ ℓ`. -/
lemma level_ge_top {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (m : ℕ) (hm : m ≤ ℓ) :
    flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) ≤
      flvl f p x m hm (W.t m hm) := by
  classical
  -- descending induction over the distance ℓ − m
  have main : ∀ (k : ℕ), k ≤ ℓ → ∀ (r : ℕ) (hr : r ≤ ℓ), ℓ - r = k →
      flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) ≤
        flvl f p x r hr (W.t r hr) := by
    intro k
    induction k with
    | zero =>
        intro hk r hr hdist
        have hreq : r = ℓ := by omega
        subst r
        have heq : flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) =
            flvl f p x ℓ hr (W.t ℓ hr) := by
          rw [flvl_hm_irrel]
          congr 1
        exact le_of_eq heq
    | succ k ih =>
        intro hk r hr hdist
        have hmlt : r < ℓ := by omega
        have h1le : r + 1 ≤ ℓ := Nat.succ_le_of_lt hmlt
        have hdist1 : ℓ - (r + 1) = k := by omega
        have hC := ih (Nat.le_trans (Nat.le_succ k) hk) (r + 1) h1le hdist1
        -- hC : top ≤ flvl (r+1) h1le (W.t (r+1) h1le)
        have hm0 := W.hmono r h1le
        -- hm0 : flvl (r+1) (succ_le_of_lt (lt_of_succ_le h1le)) (W.t (r+1) h1le) ≤
        --        flvl r (le_trans (le_succ r) h1le) (W.t r (le_trans (le_succ r) h1le))
        have hm0' : flvl f p x (r + 1) h1le (W.t (r + 1) h1le) ≤
            flvl f p x r (Nat.le_trans (Nat.le_succ r) h1le)
              (W.t r (Nat.le_trans (Nat.le_succ r) h1le)) := by
          rw [show flvl f p x (r + 1) h1le =
              flvl f p x (r + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le h1le)) by
                exact flvl_hm_irrel]
          simpa using hm0
        have hC' : flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) ≤
            flvl f p x (r + 1) h1le (W.t (r + 1) h1le) := hC
        calc
          flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ))
              ≤ flvl f p x (r + 1) h1le (W.t (r + 1) h1le) := hC'
          _ ≤ flvl f p x r (Nat.le_trans (Nat.le_succ r) h1le)
                (W.t r (Nat.le_trans (Nat.le_succ r) h1le)) := hm0'
          _ = flvl f p x r hr (W.t r hr) := by
                rw [flvl_hm_irrel]
                congr 1
  exact main (ℓ - m) (Nat.sub_le ℓ m) m hm rfl



/-- The decay-rate constant of Lemma l:aux 09019847294:
`η := log(a/b) / (2·(−log b))` with `a := 1−p+ε`, `b := 1−p+ε/2`. -/
noncomputable def ηdec (p : unitInterval) (ε : ℝ) : ℝ :=
  Real.log ((1 - (p : ℝ) + ε) / (1 - (p : ℝ) + ε / 2)) /
    (2 * (-Real.log (1 - (p : ℝ) + ε / 2)))



/-- Lemma l:aux 09019847294 (deterministic containment).  If the top value at
`t_ℓ` exceeds both `L/(N√n)` and `(1−p+ε)^ℓ·‖f‖∞`, then from `t_ℓ` one can
walk down (∃ a `BWalk`) so that at least `n·ηdec p ε` of the `ℓ` levels are
non-decaying (the number of non-decaying levels is `ℓ − decayUpTo`). -/
theorem descendant_nondecay {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε0 : 0 < ε) (hεp : ε < (p : ℝ))
    {L : ℝ} (hL0 : 0 < L) {N n : ℕ} (hN1 : 1 ≤ N) (hn1 : 1 ≤ n)
    {ℓ : ℕ} (hℓge : n ≤ 2 * ℓ) (hℓle : ℓ ≤ n)
    {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
    (hfmass : norm₁ f ≤ 1) {x : Fin ℓ → ℤ} :
    (∃ t_ℓ : ℤ,
      flvl f p x ℓ (Nat.le_refl ℓ) t_ℓ >
        max (L / ((N : ℝ) * Real.sqrt (n : ℝ)))
            (((1 - (p : ℝ) + ε) ^ ℓ) * esup f)) →
      ∃ (t_ℓ : ℤ) (W : BWalk f p x t_ℓ),
        ((ℓ : ℝ) - (decayUpTo W
          ((ε * L) / (2 * (p : ℝ) * (N : ℝ) * Real.sqrt (n : ℝ)))
          ℓ (Nat.le_refl ℓ) : ℝ)) ≥ (n : ℝ) * ηdec p ε := by
  intro h
  classical
  rcases h with ⟨t_ℓ, ht_ℓ⟩
  let W : BWalk f p x t_ℓ := backward_chain f p x t_ℓ
  let T : ℝ := (ε * L) / (2 * (p : ℝ) * (N : ℝ) * Real.sqrt (n : ℝ))
  let a : ℝ := 1 - (p : ℝ) + ε
  let b : ℝ := 1 - (p : ℝ) + ε / 2
  let u : ℕ := decayUpTo W T ℓ (Nat.le_refl ℓ)
  have hb0 : 0 ≤ b := by
    dsimp [b]
    have h1 : 0 ≤ 1 - (p : ℝ) := by linarith [p.property.2]
    nlinarith [hε0]
  have hbpos : 0 < b := by
    dsimp [b]
    have h1 : 0 ≤ 1 - (p : ℝ) := by linarith [p.property.2]
    nlinarith [hε0]
  have hba : b < a := by
    dsimp [a, b]
    linarith [hε0]
  have ha1 : a < 1 := by
    dsimp [a]
    linarith [hεp]
  have hWtop : flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) =
      flvl f p x ℓ (Nat.le_refl ℓ) t_ℓ := by
    dsimp [W]
    have hh := (backward_chain f p x t_ℓ).htop
    rw [hh]
  have hAt : L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
      flvl f p x ℓ (Nat.le_refl ℓ) t_ℓ :=
    lt_of_le_of_lt (le_max_left _ _) ht_ℓ
  have hBt : a ^ ℓ * esup f < flvl f p x ℓ (Nat.le_refl ℓ) t_ℓ := by
    have hmax : (((1 - (p : ℝ) + ε) ^ ℓ) * esup f) <
        flvl f p x ℓ (Nat.le_refl ℓ) t_ℓ :=
      lt_of_le_of_lt (le_max_right _ _) ht_ℓ
    simpa [a] using hmax
  have hbig : ∀ (m : ℕ) (hm : m ≤ ℓ),
      T ≤ (ε / (2 * (p : ℝ))) * flvl f p x m hm (W.t m hm) := by
    intro m hm
    have hge := level_ge_top W m hm
    have hAtW : L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
        flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) := by
      simpa [hWtop.symm] using hAt
    have hLlt : L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
        flvl f p x m hm (W.t m hm) :=
      lt_of_lt_of_le hAtW hge
    have hT : T = (ε / (2 * (p : ℝ))) * (L / ((N : ℝ) * Real.sqrt (n : ℝ))) := by
      dsimp [T]
      field_simp [show (N : ℝ) ≠ 0 by positivity,
        show Real.sqrt (n : ℝ) ≠ 0 by positivity,
        show (p : ℝ) ≠ 0 by positivity]
    have hmul : (ε / (2 * (p : ℝ))) * (L / ((N : ℝ) * Real.sqrt (n : ℝ))) <
        (ε / (2 * (p : ℝ))) * flvl f p x m hm (W.t m hm) :=
      mul_lt_mul_of_pos_left hLlt (by positivity)
    rw [hT]
    exact le_of_lt hmul
  have hchain := chain_value_bound W T hε0.le hp₀ hp₁ (by nlinarith) hfpos hbig
  have hchain' : flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) ≤
      b ^ u * flvl f p x 0 (Nat.zero_le ℓ) (W.t 0 (Nat.zero_le ℓ)) := by
    simpa [b, u] using hchain
  have hfl0 : flvl f p x 0 (Nat.zero_le ℓ) (W.t 0 (Nat.zero_le ℓ)) ≤ esup f := by
    have hz : flvl f p x 0 (Nat.zero_le ℓ) (W.t 0 (Nat.zero_le ℓ)) =
        f (W.t 0 (Nat.zero_le ℓ)) := flvl_zero (f := f) (p := p) (x := x)
          (W.t 0 (Nat.zero_le ℓ))
    rw [hz]
    exact le_esup hfpos hfsum (W.t 0 (Nat.zero_le ℓ))
  have hbigv : a ^ ℓ * esup f < flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) := by
    rwa [hWtop]
  have hbchain' : flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) ≤
      b ^ u * esup f := by
    exact le_trans hchain' (mul_le_mul_of_nonneg_left hfl0 (pow_nonneg hb0 u))
  have hesup0 : 0 < esup f := by
    have hposv : 0 < flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) := by
      have hn0 : 0 ≤ a ^ ℓ * esup f := by
        exact mul_nonneg (pow_nonneg (by dsimp [a]; nlinarith : 0 ≤ a) ℓ)
          (esup_nonneg hfpos hfsum)
      exact lt_of_le_of_lt hn0 hbigv
    have hge0 := level_ge_top W 0 (Nat.zero_le ℓ)
    exact lt_of_lt_of_le hposv (le_trans hge0 hfl0)
  have hpowlt : a ^ ℓ < b ^ u := by
    exact lt_of_mul_lt_mul_right (lt_of_lt_of_le hbigv hbchain') (le_of_lt hesup0)
  have hlog := Commons.Analysis.Real.log_geom_decay_steps hbpos hba ha1
    (by exact_mod_cast hn1) (by exact_mod_cast hℓge) hpowlt
  have hlt : (n : ℝ) * ηdec p ε < ((ℓ : ℝ) - (u : ℝ)) := by
    dsimp [ηdec, a, b] at hlog ⊢
    rw [← mul_div_assoc]
    exact hlog
  refine ⟨t_ℓ, backward_chain f p x t_ℓ, ?_⟩
  simpa [W, u] using (le_of_lt hlt)

end Submission.Sec3Tower
