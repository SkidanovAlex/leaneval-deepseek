/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymBilinear

/-!
# The symmetric bilinear constant: the block-extension bridge (GLYZ §3)

`AsymBilinear.lean` states the asymmetric bilinear decoupling inequality `AsymDec` with the
family `f` indexed by *all* the fine pieces (`f : Fin (2^N) → E k → ℂ`), while
`BilinearReduction.lean`'s `BilinDec` indexes a family by the `M` pieces of one coarse
interval.  This module builds the bridge between the two conventions:

* `blkMod`, `blkIdxFin` — the index of a fine piece inside its level-`m` block, and the inverse
  map `Fin (2^(N-m)) → Fin (2^N)`;
* `sum_blkFin_mod`, `sum_blkFin_fin` — the two reindexing identities for a sum over a dyadic
  block;
* `blockFam` — the extension of a family indexed by the pieces of one block to a family
  indexed by all the fine pieces (zero outside);
* **`SymDec`** — the symmetric bilinear inequality in the "glued" form in which the two coarse
  intervals are the first quarter and the `a'`-th quarter of `[0,1]` and the family is indexed
  by all the fine pieces;
* **`bilinDec_of_symDec`** and **`symDec_of_bilinDec`** — the two directions of the equivalence
  between `SymDec k N C` and `BilinDec k (2^(N-2)) C`.

This is the GLYZ §3 interface: Lemma 3.4 produces `SymDec` out of `AsymDec`, and the induction
of §4 consumes `BilinDec` through `LinearFromBilinear.decLin_of_bilinDec`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. The index of a fine piece inside its coarse block -/

/-- The position of `i` inside its level-`m` block, i.e. the residue modulo `2^(N-m)`.  It is
only meaningful when `i` does lie in a level-`m` block, which is the only way it is used. -/
def blkMod (N m : ℕ) (i : Fin (2 ^ N)) : Fin (2 ^ (N - m)) :=
  ⟨(i : ℕ) % 2 ^ (N - m), Nat.mod_lt _ (pow_pos (by norm_num) (N - m))⟩

/-- The inverse of `blkMod`: the `j`-th fine piece of the level-`m` block `q`. -/
def blkIdxFin (N m q : ℕ) (j : Fin (2 ^ (N - m))) : Fin (2 ^ N) :=
  ⟨(q * 2 ^ (N - m) + (j : ℕ)) % 2 ^ N, Nat.mod_lt _ (pow_pos (by norm_num) N)⟩

lemma blkMod_val {N m q : ℕ} {i : Fin (2 ^ N)} (hi : i ∈ blkFin N m q) :
    q * 2 ^ (N - m) + (blkMod N m i : ℕ) = (i : ℕ) := by
  have h1 : (i : ℕ) / 2 ^ (N - m) = q := mem_blkFin.mp hi
  have h2 := Nat.div_add_mod (i : ℕ) (2 ^ (N - m))
  rw [h1, Nat.mul_comm] at h2
  simpa only [blkMod, Fin.val_mk] using h2

lemma blkIdxFin_val {N m q : ℕ} (hm : m ≤ N) (hq : q < 2 ^ m) (j : Fin (2 ^ (N - m))) :
    (blkIdxFin N m q j : ℕ) = q * 2 ^ (N - m) + (j : ℕ) := by
  rw [blkIdxFin]
  exact Nat.mod_eq_of_lt (blockIdx_lt hm rfl hq j.2)

lemma blkIdxFin_eq {N m q : ℕ} (hm : m ≤ N) (hq : q < 2 ^ m) (j : Fin (2 ^ (N - m))) :
    blkIdxFin N m q j
      = ⟨q * 2 ^ (N - m) + (j : ℕ), blockIdx_lt hm rfl hq j.2⟩ :=
  Fin.ext (blkIdxFin_val hm hq j)

lemma blkIdxFin_mem {N m q : ℕ} (hm : m ≤ N) (hq : q < 2 ^ m) (j : Fin (2 ^ (N - m))) :
    blkIdxFin N m q j ∈ blkFin N m q := by
  rw [mem_blkFin]
  have h := blkIdxFin_val hm hq j
  rw [h]
  have hlt : q * 2 ^ (N - m) + (j : ℕ) < (q + 1) * 2 ^ (N - m) := by
    rw [Nat.succ_mul]
    exact Nat.add_lt_add_left j.2 _
  exact Nat.div_eq_of_lt_le (Nat.le_add_right _ _) hlt

lemma blkMod_blkIdxFin {N m q : ℕ} (hm : m ≤ N) (hq : q < 2 ^ m) (j : Fin (2 ^ (N - m))) :
    blkMod N m (blkIdxFin N m q j) = j := by
  have h := blkMod_val (blkIdxFin_mem hm hq j)
  rw [blkIdxFin_val hm hq j] at h
  exact Fin.ext (by omega)

lemma blkIdxFin_blkMod {N m q : ℕ} (hm : m ≤ N) (hq : q < 2 ^ m) {i : Fin (2 ^ N)}
    (hi : i ∈ blkFin N m q) : blkIdxFin N m q (blkMod N m i) = i := by
  have h := blkMod_val hi
  exact Fin.ext (by rw [blkIdxFin_val hm hq, h])

/-! ## 2. Reindexing a dyadic block -/

/-- Reindexing a block sum by the residues `i % 2^(N-m)`. -/
lemma sum_blkFin_mod {N m q : ℕ} (hm : m ≤ N) (hq : q < 2 ^ m)
    {α : Type*} [AddCommMonoid α] (F : Fin (2 ^ (N - m)) → α) :
    ∑ i ∈ blkFin N m q, F (blkMod N m i) = ∑ j, F j := by
  refine Finset.sum_bij (fun (i : Fin (2 ^ N)) _ => blkMod N m i) ?_ ?_ ?_ ?_
  · intro i hi; exact Finset.mem_univ _
  · intro i₁ hi₁ i₂ hi₂ heq
    refine Fin.ext ?_
    have h₁ := blkMod_val hi₁
    have h₂ := blkMod_val hi₂
    have h₃ : (blkMod N m i₁ : ℕ) = (blkMod N m i₂ : ℕ) := by rw [heq]
    omega
  · intro j hj
    exact ⟨blkIdxFin N m q j, blkIdxFin_mem hm hq j, blkMod_blkIdxFin hm hq j⟩
  · intro a ha; rfl

/-- Reindexing a block sum by the fine pieces of the block. -/
lemma sum_blkFin_fin {N m q : ℕ} (hm : m ≤ N) (hq : q < 2 ^ m)
    {α : Type*} [AddCommMonoid α] (G : Fin (2 ^ N) → α) :
    ∑ i ∈ blkFin N m q, G i = ∑ j : Fin (2 ^ (N - m)), G (blkIdxFin N m q j) := by
  refine Finset.sum_bij (fun (i : Fin (2 ^ N)) _ => blkMod N m i) ?_ ?_ ?_ ?_
  · intro i hi; exact Finset.mem_univ _
  · intro i₁ hi₁ i₂ hi₂ heq
    refine Fin.ext ?_
    have h₁ := blkMod_val hi₁
    have h₂ := blkMod_val hi₂
    have h₃ : (blkMod N m i₁ : ℕ) = (blkMod N m i₂ : ℕ) := by rw [heq]
    omega
  · intro j hj
    exact ⟨blkIdxFin N m q j, blkIdxFin_mem hm hq j, blkMod_blkIdxFin hm hq j⟩
  · intro a ha
    rw [blkIdxFin_blkMod hm hq ha]

/-- The `ℓ²` quantity of a dyadic block, in the coordinates of the block. -/
lemma l2Of_blkFin_fin {k N m q : ℕ} (hm : m ≤ N) (hq : q < 2 ^ m)
    (G : Fin (2 ^ N) → E k → ℂ) :
    l2Of (blkFin N m q) (fun i => lpNorm k (pE k) (G i))
      = l2Norm (fun j : Fin (2 ^ (N - m)) => lpNorm k (pE k) (G (blkIdxFin N m q j))) := by
  rw [l2Of, l2Norm, sqSum]
  congr 1
  exact sum_blkFin_fin hm hq (fun i => (lpNorm k (pE k) (G i)) ^ (2 : ℝ))

lemma l2Of_congr {ι : Type*} {s : Finset ι} {a b : ι → ℝ≥0∞} (h : ∀ i ∈ s, a i = b i) :
    l2Of s a = l2Of s b := by
  rw [l2Of, l2Of, sqSum, sqSum]
  congr 1
  exact Finset.sum_congr rfl fun i hi => by rw [h i hi]

/-! ## 3. Extending a family supported on a block -/

/-- The extension of a family indexed by the `2^(N-m)` pieces of one level-`m` block to a
family indexed by all the `2^N` fine pieces (zero off the block). -/
def blockFam (k N m q : ℕ) (f : Fin (2 ^ (N - m)) → E k → ℂ) : Fin (2 ^ N) → E k → ℂ :=
  fun i => if (i : ℕ) / 2 ^ (N - m) = q then f (blkMod N m i) else 0

lemma blockFam_apply_mem {k N m q : ℕ} {i : Fin (2 ^ N)} (hi : i ∈ blkFin N m q)
    (f : Fin (2 ^ (N - m)) → E k → ℂ) : blockFam k N m q f i = f (blkMod N m i) := by
  rw [blockFam, if_pos (mem_blkFin.mp hi)]

lemma blockFam_eq_zero {k N m q : ℕ} {i : Fin (2 ^ N)} (hi : (i : ℕ) / 2 ^ (N - m) ≠ q)
    (f : Fin (2 ^ (N - m)) → E k → ℂ) : blockFam k N m q f i = 0 := by
  rw [blockFam, if_neg hi]

lemma sum_blockFam {k N m q : ℕ} (hm : m ≤ N) (hq : q < 2 ^ m)
    (f : Fin (2 ^ (N - m)) → E k → ℂ) :
    ∑ i ∈ blkFin N m q, blockFam k N m q f i = ∑ j, f j :=
  (Finset.sum_congr rfl fun i hi => blockFam_apply_mem hi f).trans
    (sum_blkFin_mod hm hq f)

lemma sum_blockFam_apply {k N m q : ℕ} (hm : m ≤ N) (hq : q < 2 ^ m)
    (f : Fin (2 ^ (N - m)) → E k → ℂ) (x : E k) :
    ∑ i ∈ blkFin N m q, blockFam k N m q f i x = ∑ j, f j x := by
  rw [← Finset.sum_apply, sum_blockFam hm hq f, Finset.sum_apply]

lemma l2Of_blockFam {k N m q : ℕ} (hm : m ≤ N) (hq : q < 2 ^ m)
    (f : Fin (2 ^ (N - m)) → E k → ℂ) :
    l2Of (blkFin N m q) (fun i => lpNorm k (pE k) (blockFam k N m q f i))
      = l2Norm (fun j : Fin (2 ^ (N - m)) => lpNorm k (pE k) (f j)) := by
  rw [l2Of_blkFin_fin hm hq (blockFam k N m q f)]
  exact congrArg l2Norm (funext fun j => by
    rw [blockFam_apply_mem (blkIdxFin_mem hm hq j) f, blkMod_blkIdxFin hm hq j])

/-! ## 4. The plates of a dyadic block -/

/-- The plate of the `j`-th fine piece of the level-`2` block `a` is the `j`-th sub-plate of the
quarter `a`. -/
lemma piecePlate_eq_subPlate {k N : ℕ} (hN : 2 ≤ N) (a : Fin 4) (j : Fin (2 ^ (N - 2))) :
    piecePlate k (2 ^ N)
        ⟨(a : ℕ) * 2 ^ (N - 2) + (j : ℕ),
          blockIdx_lt (N := N) (n := 2) (q := (a : ℕ)) (M := 2 ^ (N - 2)) (j := (j : ℕ))
            hN rfl a.2 j.2⟩
      = subPlate k (2 ^ (N - 2)) a j := by
  have h := piecePlate_block (k := k) (N := N) (n := 2) (q := (a : ℕ)) (M := 2 ^ (N - 2))
    hN rfl a.2 j
  rw [subPlate, subCenter, h]
  apply plate_congr'
  · field_simp
    norm_num
  · push_cast
    field_simp
    ring

lemma piecePlate_blkIdxFin {k N : ℕ} (hN : 2 ≤ N) {q : ℕ} (hq : q < 4)
    (j : Fin (2 ^ (N - 2))) :
    piecePlate k (2 ^ N) (blkIdxFin N 2 q j) = subPlate k (2 ^ (N - 2)) ⟨q, hq⟩ j := by
  rw [blkIdxFin_eq (N := N) (m := 2) (q := q) hN (by simpa using hq) j]
  exact piecePlate_eq_subPlate (k := k) hN ⟨q, hq⟩ j

/-- The plate of a fine piece of the level-`2` block `a`, in terms of the residue. -/
lemma piecePlate_eq_subPlate_of_div {k N : ℕ} (hN : 2 ≤ N) (a : Fin 4) {i : Fin (2 ^ N)}
    (hi : (i : ℕ) / 2 ^ (N - 2) = (a : ℕ)) :
    piecePlate k (2 ^ N) i = subPlate k (2 ^ (N - 2)) a (blkMod N 2 i) := by
  have hval : ((a : ℕ) * 2 ^ (N - 2) + (blkMod N 2 i : ℕ)) = (i : ℕ) := by
    have h := Nat.div_add_mod (i : ℕ) (2 ^ (N - 2))
    rw [hi, Nat.mul_comm] at h
    simpa only [blkMod, Fin.val_mk] using h
  have hfin : (⟨(a : ℕ) * 2 ^ (N - 2) + (blkMod N 2 i : ℕ),
      blockIdx_lt (N := N) (n := 2) (q := (a : ℕ)) (M := 2 ^ (N - 2))
        (j := (blkMod N 2 i : ℕ)) hN rfl a.2 (blkMod N 2 i).2⟩ : Fin (2 ^ N)) = i :=
    Fin.ext hval
  conv_lhs => rw [← hfin]
  exact piecePlate_eq_subPlate hN a (blkMod N 2 i)

/-! ## 5. The symmetric bilinear constant in glued form -/

/-- The symmetric bilinear decoupling inequality in the form in which the two coarse intervals
are the first and the `a'`-th quarter of `[0,1]` and the family is indexed by *all* the fine
pieces.  It is `BilinDec k (2^(N-2))` with the two quarter-families glued together. -/
def SymDec (k N : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ (a' : Fin 4), 2 ≤ (a' : ℕ) →
  ∀ (f : Fin (2 ^ N) → E k → ℂ),
    (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
    (∫⁻ x, ((‖(∑ i ∈ blkFin N 2 0, f i x)‖₊ : ℝ≥0∞) ^ ((k : ℝ) * ((k : ℝ) + 1) / 2))
        * ((‖(∑ i ∈ blkFin N 2 (a' : ℕ), f i x)‖₊ : ℝ≥0∞) ^ ((k : ℝ) * ((k : ℝ) + 1) / 2)))
      ≤ C ^ ((k : ℝ) * ((k : ℝ) + 1))
          * (l2Of (blkFin N 2 0) (fun i => lpNorm k (pE k) (f i)))
              ^ ((k : ℝ) * ((k : ℝ) + 1) / 2)
          * (l2Of (blkFin N 2 (a' : ℕ)) (fun i => lpNorm k (pE k) (f i)))
              ^ ((k : ℝ) * ((k : ℝ) + 1) / 2)

lemma symDec_mono {k N : ℕ} {C C' : ℝ≥0∞} (h : C ≤ C') (hS : SymDec k N C) :
    SymDec k N C' := by
  intro a' ha' f hf
  refine (hS a' ha' f hf).trans ?_
  refine mul_le_mul' (mul_le_mul_left (ENNReal.rpow_le_rpow h (by positivity)) _) le_rfl

/-- **The glued form implies `BilinDec`** (no loss). -/
theorem bilinDec_of_symDec {k N : ℕ} (hN : 2 ≤ N) {C : ℝ≥0∞} (hS : SymDec k N C) :
    BilinDec k (2 ^ (N - 2)) C := by
  intro a' ha' f f' hf hf'
  classical
  set g : Fin (2 ^ N) → E k → ℂ := fun i =>
    blockFam k N 2 0 f i + blockFam k N 2 (a' : ℕ) f' i with hgdef
  have hgd : ∀ i, g i = blockFam k N 2 0 f i + blockFam k N 2 (a' : ℕ) f' i := fun i => rfl
  have hne0 : ∀ i : Fin (2 ^ N), (i : ℕ) / 2 ^ (N - 2) = 0 → (i : ℕ) / 2 ^ (N - 2) ≠ (a' : ℕ) := by
    intro i hc h
    rw [h] at hc
    omega
  have hrep : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (g i) := by
    intro i
    by_cases hc : (i : ℕ) / 2 ^ (N - 2) = 0
    · have hne := hne0 i hc
      have hgi : g i = f (blkMod N 2 i) := by
        funext x
        simp only [hgd, Pi.add_apply, blockFam_apply_mem (mem_blkFin.mpr hc) f,
          blockFam_eq_zero hne f', Pi.zero_apply, add_zero]
      rw [hgi, piecePlate_eq_subPlate_of_div (k := k) hN 0 hc]
      exact hf (blkMod N 2 i)
    · by_cases hc' : (i : ℕ) / 2 ^ (N - 2) = (a' : ℕ)
      · have hgi : g i = f' (blkMod N 2 i) := by
          funext x
          simp only [hgd, Pi.add_apply, blockFam_eq_zero hc f,
            blockFam_apply_mem (mem_blkFin.mpr hc') f', Pi.zero_apply, zero_add]
        rw [hgi, piecePlate_eq_subPlate_of_div (k := k) hN a' hc']
        exact hf' (blkMod N 2 i)
      · have hgi : g i = 0 := by
          funext x
          simp only [hgd, Pi.add_apply, blockFam_eq_zero hc f, blockFam_eq_zero hc' f', Pi.zero_apply, add_zero]
        rw [hgi]
        exact IsFourierRep.zero k _
  have hsum0 : ∀ x : E k, ∑ i ∈ blkFin N 2 0, g i x = ∑ j, f j x := by
    intro x
    have h₁ : ∀ i ∈ blkFin N 2 0, blockFam k N 2 (a' : ℕ) f' i = 0 := fun i hi =>
      blockFam_eq_zero (hne0 i (mem_blkFin.mp hi)) f'
    rw [← Finset.sum_apply, Finset.sum_congr rfl (fun i _ => hgd i), Finset.sum_add_distrib,
      sum_blockFam (k := k) (N := N) (m := 2) (q := 0) (by omega) (by norm_num) f,
      Finset.sum_eq_zero h₁, add_zero, Finset.sum_apply]
  have hsuma : ∀ x : E k, ∑ i ∈ blkFin N 2 (a' : ℕ), g i x = ∑ j, f' j x := by
    intro x
    have h₁ : ∀ i ∈ blkFin N 2 (a' : ℕ), blockFam k N 2 0 f i = 0 := by
      intro i hi
      refine blockFam_eq_zero (i := i) (m := 2) (q := 0) ?_ f
      have h2 : (i : ℕ) / 2 ^ (N - 2) = (a' : ℕ) := mem_blkFin.mp hi
      rw [h2]
      omega
    rw [← Finset.sum_apply, Finset.sum_congr rfl (fun i _ => hgd i), Finset.sum_add_distrib,
      Finset.sum_eq_zero h₁,
      sum_blockFam (k := k) (N := N) (m := 2) (q := (a' : ℕ)) (by omega) a'.2 f',
      zero_add, Finset.sum_apply]
  have hl2a : l2Of (blkFin N 2 (a' : ℕ)) (fun i => lpNorm k (pE k) (g i))
      = l2Norm (fun j : Fin (2 ^ (N - 2)) => lpNorm k (pE k) (f' j)) := by
    refine (l2Of_congr ?_).trans (l2Of_blockFam (k := k) (by omega) a'.2 f')
    intro i hi
    have hc' : (i : ℕ) / 2 ^ (N - 2) = (a' : ℕ) := mem_blkFin.mp hi
    have hc : (i : ℕ) / 2 ^ (N - 2) ≠ 0 := by rw [hc']; omega
    have hgi : g i = blockFam k N 2 (a' : ℕ) f' i := by
      funext x
      simp only [hgd, Pi.add_apply, blockFam_eq_zero hc f,
        blockFam_apply_mem (mem_blkFin.mpr hc') f', Pi.zero_apply, zero_add]
    rw [hgi]
  have hl20 : l2Of (blkFin N 2 0) (fun i => lpNorm k (pE k) (g i))
      = l2Norm (fun j : Fin (2 ^ (N - 2)) => lpNorm k (pE k) (f j)) := by
    refine (l2Of_congr ?_).trans (l2Of_blockFam (k := k) (by omega) (by norm_num) f)
    intro i hi
    have hc : (i : ℕ) / 2 ^ (N - 2) = 0 := mem_blkFin.mp hi
    have hgi : g i = blockFam k N 2 0 f i := by
      funext x
      simp only [hgd, Pi.add_apply, blockFam_apply_mem (mem_blkFin.mpr hc) f,
        blockFam_eq_zero (hne0 i hc) f', Pi.zero_apply, add_zero]
    rw [hgi]
  have h := hS a' ha' g hrep
  have hL : (∫⁻ x, ((‖(∑ j : Fin (2 ^ (N - 2)), f j x)‖₊ : ℝ≥0∞)
        ^ ((k : ℝ) * ((k : ℝ) + 1) / 2))
      * ((‖(∑ j : Fin (2 ^ (N - 2)), f' j x)‖₊ : ℝ≥0∞)
        ^ ((k : ℝ) * ((k : ℝ) + 1) / 2)))
    = ∫⁻ x, ((‖(∑ i ∈ blkFin N 2 0, g i x)‖₊ : ℝ≥0∞)
        ^ ((k : ℝ) * ((k : ℝ) + 1) / 2))
      * ((‖(∑ i ∈ blkFin N 2 (a' : ℕ), g i x)‖₊ : ℝ≥0∞)
        ^ ((k : ℝ) * ((k : ℝ) + 1) / 2)) := by
    refine lintegral_congr fun x => ?_
    rw [hsum0 x, hsuma x]
  rw [hL, ← hl20, ← hl2a]
  exact h

/-- **`BilinDec` implies the glued form** (no loss). -/
theorem symDec_of_bilinDec {k N : ℕ} (hN : 2 ≤ N) {C : ℝ≥0∞}
    (hB : BilinDec k (2 ^ (N - 2)) C) : SymDec k N C := by
  intro a' ha' g hg
  classical
  set f : Fin (2 ^ (N - 2)) → E k → ℂ := fun j => g (blkIdxFin N 2 0 j) with hfdef
  set f' : Fin (2 ^ (N - 2)) → E k → ℂ := fun j => g (blkIdxFin N 2 (a' : ℕ) j) with hf'def
  have hfrepr : ∀ j, IsFourierRep k (subPlate k (2 ^ (N - 2)) 0 j) (f j) := by
    intro j
    have h := hg (blkIdxFin N 2 0 j)
    simpa only [hfdef] using (piecePlate_blkIdxFin (k := k) hN (q := (0:ℕ)) (by norm_num) j) ▸ h
  have hf'repr : ∀ j, IsFourierRep k (subPlate k (2 ^ (N - 2)) a' j) (f' j) := by
    intro j
    have h := hg (blkIdxFin N 2 (a' : ℕ) j)
    simpa only [hf'def] using
      (piecePlate_blkIdxFin (k := k) hN (q := (a' : ℕ)) a'.2 j) ▸ h
  have hsum0 : ∀ x : E k, ∑ i ∈ blkFin N 2 0, g i x = ∑ j, f j x := by
    intro x
    have h := sum_blkFin_fin (N := N) (m := 2) (q := 0) (by omega)
      (by norm_num : (0:ℕ) < 2 ^ 2) (fun i => g i x)
    exact h
  have hsuma : ∀ x : E k, ∑ i ∈ blkFin N 2 (a' : ℕ), g i x = ∑ j, f' j x := by
    intro x
    have h := sum_blkFin_fin (N := N) (m := 2) (q := (a' : ℕ)) (by omega)
      (by have h := a'.2; omega) (fun i => g i x)
    exact h
  have hl20 : l2Of (blkFin N 2 0) (fun i => lpNorm k (pE k) (g i))
      = l2Norm (fun j : Fin (2 ^ (N - 2)) => lpNorm k (pE k) (f j)) := by
    have h := l2Of_blkFin_fin (k := k) (N := N) (m := 2) (q := 0) (by omega)
      (by norm_num : (0:ℕ) < 2 ^ 2) g
    exact h
  have hl2a : l2Of (blkFin N 2 (a' : ℕ)) (fun i => lpNorm k (pE k) (g i))
      = l2Norm (fun j : Fin (2 ^ (N - 2)) => lpNorm k (pE k) (f' j)) := by
    have h := l2Of_blkFin_fin (k := k) (N := N) (m := 2) (q := (a' : ℕ)) (by omega)
      (by have h := a'.2; omega) g
    exact h
  have h := hB a' ha' f f' hfrepr hf'repr
  have hL : (∫⁻ x, ((‖(∑ i ∈ blkFin N 2 0, g i x)‖₊ : ℝ≥0∞)
        ^ ((k : ℝ) * ((k : ℝ) + 1) / 2))
      * ((‖(∑ i ∈ blkFin N 2 (a' : ℕ), g i x)‖₊ : ℝ≥0∞)
        ^ ((k : ℝ) * ((k : ℝ) + 1) / 2)))
    = ∫⁻ x, ((‖(∑ j : Fin (2 ^ (N - 2)), f j x)‖₊ : ℝ≥0∞)
        ^ ((k : ℝ) * ((k : ℝ) + 1) / 2))
      * ((‖(∑ j : Fin (2 ^ (N - 2)), f' j x)‖₊ : ℝ≥0∞)
        ^ ((k : ℝ) * ((k : ℝ) + 1) / 2)) := by
    refine lintegral_congr fun x => ?_
    rw [hsum0 x, hsuma x]
  rw [hL, hl20, hl2a]
  exact h

end Submission.Vinogradov
