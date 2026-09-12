import Mathlib
import Submission.Contracts
import Submission.WnormToolkit

/-!
# Generic helpers for STAGE 2b of `core_squarefree`

* root-counting for complex polynomials among the naturals `< n`;
* existence of a `(n − deg)`-subset of non-roots of the naturals `< n`;
* degree of `A.primPart · ∏_{s∈S} (X − C s)`;
* weighted-norm bounds for products by integer-linear factors and for the
  primitive-part content factor.

Namespace `Submission.SqfStage2` (local helpers; the general ones are also
published to the commons when self-contained).
-/

noncomputable section
open scoped Real BigOperators
open Polynomial

namespace Submission.SqfStage2

open Submission.Contracts
open Submission.WnormToolkit
open Submission.WeightedNorm
open Submission.SerreExample

/-- Mapping `zmap A` (the ℤ→ℝ map) further to ℂ equals the ℤ→ℂ map of `A`. -/
lemma zmap_map_eq_map (A : Polynomial ℤ) :
    (zmap A).map (algebraMap ℝ ℂ) = A.map (algebraMap ℤ ℂ) := by
  calc
    (zmap A).map (algebraMap ℝ ℂ) = A.map ((algebraMap ℝ ℂ).comp (algebraMap ℤ ℝ)) := by
      simp [zmap, Polynomial.map_map]
    _ = A.map (algebraMap ℤ ℂ) := by
      rfl


/-- A nonzero complex polynomial vanishes at at most `natDegree` of the
natural numbers `< n`. -/
lemma root_count_le {f : Polynomial ℂ} (hf : f ≠ 0) (n : ℕ) :
    ((Finset.range n).filter (fun s : ℕ => Polynomial.aeval (s : ℂ) f = 0)).card ≤ f.natDegree := by
  classical
  let R : Finset ℕ := (Finset.range n).filter (fun s : ℕ => Polynomial.aeval (s : ℂ) f = 0)
  let T : Finset ℂ := f.roots.toFinset
  have hmap : Set.MapsTo (fun s : ℕ => (s : ℂ)) (↑R : Set ℕ) (↑T : Set ℂ) := by
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    have hroot : (z : ℂ) ∈ f.roots :=
      (Polynomial.mem_roots_iff_aeval_eq_zero hf).mpr hz'
    simpa [T] using hroot
  have hinj : Set.InjOn (fun s : ℕ => (s : ℂ)) (↑R : Set ℕ) := by
    intro a ha b hb hab
    exact Nat.cast_injective hab
  have hcardR : R.card ≤ T.card :=
    Finset.card_le_card_of_injOn (fun s : ℕ => (s : ℂ)) hmap hinj
  calc
    ((Finset.range n).filter (fun s : ℕ => Polynomial.aeval (s : ℂ) f = 0)).card = R.card := rfl
    _ ≤ T.card := hcardR
    _ ≤ f.roots.card := Multiset.toFinset_card_le f.roots
    _ ≤ f.natDegree := Polynomial.card_roots' f

/-- There is a subset `S` of the naturals `< n`, of size `n − deg f`, on which
`f` does not vanish (complex sense). -/
lemma exists_nonroot_subset {f : Polynomial ℂ} (hf : f ≠ 0) (n : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ S.card = n - f.natDegree ∧
      ∀ s ∈ S, ¬ Polynomial.aeval (s : ℂ) f = 0 := by
  classical
  let Roots : Finset ℕ := (Finset.range n).filter (fun s : ℕ => Polynomial.aeval (s : ℂ) f = 0)
  let NonRoots : Finset ℕ := (Finset.range n).filter (fun s : ℕ => ¬ Polynomial.aeval (s : ℂ) f = 0)
  have hroots : Roots.card ≤ f.natDegree := by
    simpa [Roots] using root_count_le hf n
  have hcover : Roots ∪ NonRoots = Finset.range n := by
    ext z
    constructor
    · intro h
      rcases Finset.mem_union.mp h with hz | hz
      · exact (Finset.mem_filter.mp hz).1
      · exact (Finset.mem_filter.mp hz).1
    · intro hzr
      by_cases hz : Polynomial.aeval (z : ℂ) f = 0
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hzr, hz⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hzr, hz⟩))
  have hdisj : Disjoint Roots NonRoots := by
    rw [Finset.disjoint_left]
    intro z hz hzn
    exact (Finset.mem_filter.mp hzn).2 (Finset.mem_filter.mp hz).2
  have hcard2 : Roots.card + NonRoots.card = n := by
    calc
      Roots.card + NonRoots.card = (Roots ∪ NonRoots).card := by
        rw [Finset.card_union_of_disjoint hdisj]
      _ = (Finset.range n).card := by rw [hcover]
      _ = n := Finset.card_range n
  have hcard : NonRoots.card = n - Roots.card := by omega
  have hle : n - f.natDegree ≤ NonRoots.card := by
    rw [hcard]
    exact Nat.sub_le_sub_left hroots n
  rcases Finset.exists_subset_card_eq hle with ⟨S, hSsub, hScard⟩
  refine ⟨S, ?_, ?_, ?_⟩
  · exact le_trans hSsub (Finset.filter_subset (fun s : ℕ => ¬ Polynomial.aeval (s : ℂ) f = 0) (Finset.range n))
  · simpa [NonRoots] using hScard
  · intro s hs
    have hs' : s ∈ NonRoots := hSsub hs
    exact (Finset.mem_filter.mp hs').2

/-- The product of the linear factors `X − C s` (`s ∈ S`) has degree `S.card`. -/
lemma linear_prod_natDegree (S : Finset ℕ) :
    (S.prod (fun s : ℕ => (X - C (s : ℤ) : Polynomial ℤ))).natDegree = S.card := by
  classical
  have hmon : ∀ i ∈ S, ((fun s : ℕ => (X - C (s : ℤ) : Polynomial ℤ)) i).Monic := by
    intro i hi
    exact Polynomial.monic_X_sub_C (i : ℤ)
  have hdeg := Polynomial.natDegree_prod_of_monic S
    (fun s : ℕ => (X - C (s : ℤ) : Polynomial ℤ)) hmon
  calc
    (S.prod (fun s : ℕ => (X - C (s : ℤ) : Polynomial ℤ))).natDegree
        = (∏ x ∈ S, (X - C (x : ℤ) : Polynomial ℤ)).natDegree := by
            simp
    _ = ∑ x ∈ S, (X - C (x : ℤ) : Polynomial ℤ).natDegree := hdeg
    _ = ∑ x ∈ S, (1 : ℕ) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      exact Polynomial.natDegree_X_sub_C (x : ℤ)
    _ = S.card := by simp

/-- The degree of `A.primPart · ∏_{s∈S}(X − C s)` is `A.natDegree + S.card`. -/
lemma natDegree_primPart_mul_linear (A : Polynomial ℤ) (hA : A ≠ 0) (S : Finset ℕ) :
    (A.primPart * S.prod (fun s : ℕ => (X - C (s : ℤ) : Polynomial ℤ))).natDegree =
      A.natDegree + S.card := by
  classical
  have hpr : A.primPart ≠ 0 := Polynomial.primPart_ne_zero A
  let P : Polynomial ℤ := S.prod (fun s : ℕ => (X - C (s : ℤ) : Polynomial ℤ))
  have hmon : P.Monic := by
    dsimp [P]
    exact Polynomial.monic_prod_of_monic S (fun s : ℕ => (X - C (s : ℤ) : Polynomial ℤ))
      (by intro i hi; exact Polynomial.monic_X_sub_C (i : ℤ))
  have hP : P ≠ 0 := hmon.ne_zero
  have hmul : (A.primPart * P).natDegree = A.primPart.natDegree + P.natDegree :=
    Polynomial.natDegree_mul hpr hP
  calc
    (A.primPart * S.prod (fun s : ℕ => (X - C (s : ℤ) : Polynomial ℤ))).natDegree
        = A.primPart.natDegree + P.natDegree := by simpa [P] using hmul
    _ = A.natDegree + S.card := by
      rw [Polynomial.natDegree_primPart]
      congr 1
      exact linear_prod_natDegree S

/-- The real weight is nonnegative at every point of the interval. -/
lemma weight_nonneg (x : ℝ) : 0 ≤ weight muSerre x := le_of_lt (weight_pos muSerre x)

/-- Weighted norm of `Q · ∏_{s∈S}(X − C s)` is at most `‖Q‖_k · V^{S.card}`,
provided `V` bounds `|x − s|` for `x ∈ [aSerre,bSerre]` and `s ∈ S`. -/
lemma wnorm_linear_prod_le {k : ℕ} (Q : Polynomial ℝ) (V : ℝ) (hV0 : 0 ≤ V)
    (S : Finset ℕ) (hV : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → ∀ s ∈ S, |x - (s : ℝ)| ≤ V) :
    wnorm k (Q * S.prod (fun s : ℕ => (X - C (s : ℝ) : Polynomial ℝ))) ≤ wnorm k Q * V ^ S.card := by
  classical
  apply wnorm_sSup_le
  intro x hx
  have hw0 : 0 ≤ (weight muSerre x) ^ k := pow_nonneg (weight_nonneg x) k
  have hprod_le : ∏ s ∈ S, |x - (s : ℝ)| ≤ V ^ S.card := by
    calc
      ∏ s ∈ S, |x - (s : ℝ)| ≤ ∏ s ∈ S, V := by
        exact Finset.prod_le_prod (fun s hs => abs_nonneg _) (fun s hs => hV x hx s hs)
      _ = V ^ S.card := by simp
  have hprod_abs : |(S.prod (fun s : ℕ => (X - C (s : ℝ) : Polynomial ℝ))).eval x| =
      ∏ s ∈ S, |x - (s : ℝ)| := by
    rw [Polynomial.eval_prod S (fun s : ℕ => (X - C (s : ℝ) : Polynomial ℝ)) x]
    rw [Finset.abs_prod]
    simp
  calc
    (weight muSerre x) ^ k * |(Q * S.prod (fun s : ℕ => (X - C (s : ℝ) : Polynomial ℝ))).eval x|
        = (weight muSerre x) ^ k * (|Q.eval x| * |(S.prod (fun s : ℕ => (X - C (s : ℝ) : Polynomial ℝ))).eval x|) := by
            rw [Polynomial.eval_mul]
            simp [abs_mul]
    _ = (weight muSerre x) ^ k * (|Q.eval x| * ∏ s ∈ S, |x - (s : ℝ)|) := by
            rw [hprod_abs]
    _ = ((weight muSerre x) ^ k * |Q.eval x|) * ∏ s ∈ S, |x - (s : ℝ)| := by ring
    _ ≤ ((weight muSerre x) ^ k * |Q.eval x|) * V ^ S.card := by
      exact mul_le_mul_of_nonneg_left hprod_le (mul_nonneg hw0 (abs_nonneg _))
    _ ≤ wnorm k Q * V ^ S.card := by
      exact mul_le_mul_of_nonneg_right (wnorm_ge_pointwise k Q hx) (pow_nonneg hV0 S.card)

lemma wnorm_primPart_mul_le (k : ℕ) (A : Polynomial ℤ) (hA : A ≠ 0) (B : Polynomial ℤ) :
    wnorm k (zmap (A.primPart * B)) ≤ wnorm k (zmap (A * B)) := by
  classical
  apply wnorm_sSup_le
  intro x hx
  have hcont : A.content ≠ 0 := by
    intro hz
    exact hA ((Polynomial.content_eq_zero_iff).mp hz)
  have hcabs : (1 : ℝ) ≤ |(A.content : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hcont)
  have hmul : zmap (A * B) = Polynomial.C ((A.content : ℝ)) * zmap (A.primPart * B) := by
    calc
      zmap (A * B) = zmap A * zmap B := by simp [zmap, Polynomial.map_mul]
      _ = (Polynomial.C ((A.content : ℝ)) * zmap (A.primPart)) * zmap B := by
        congr 1
        calc
          zmap A = (C (A.content : ℤ) * A.primPart).map (algebraMap ℤ ℝ) := by
            congr 1
            exact Polynomial.eq_C_content_mul_primPart A
          _ = Polynomial.C ((A.content : ℝ)) * zmap A.primPart := by simp [zmap]
      _ = Polynomial.C ((A.content : ℝ)) * (zmap (A.primPart) * zmap B) := by ring
      _ = Polynomial.C ((A.content : ℝ)) * zmap (A.primPart * B) := by
        congr 1
        simp [zmap, Polynomial.map_mul]
  have hval : |(zmap (A.primPart * B)).eval x| ≤ |(zmap (A * B)).eval x| := by
    rw [hmul]
    simp
    have hz0 : 0 ≤ |(zmap (A.primPart * B)).eval x| := abs_nonneg _
    simpa using (mul_le_mul_of_nonneg_right hcabs hz0)
  calc
    (weight muSerre x) ^ k * |(zmap (A.primPart * B)).eval x|
        ≤ (weight muSerre x) ^ k * |(zmap (A * B)).eval x| := by
            exact mul_le_mul_of_nonneg_left hval (pow_nonneg (weight_nonneg x) k)
    _ ≤ wnorm k (zmap (A * B)) := wnorm_ge_pointwise k (zmap (A * B)) hx

/-- Bound `|x − s| ≤ bSerre + n` for `x ∈ [aSerre,bSerre]` and `s < n`. -/
lemma abs_sub_le_bSerre_add_n {x : ℝ} {s n : ℕ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hs : s < n) : |x - (s : ℝ)| ≤ bSerre + (n : ℝ) := by
  rcases hx with ⟨hxlo, hxhi⟩
  have hx0 : 0 ≤ x := le_trans (le_of_lt aSerre_pos) hxlo
  have hs0 : 0 ≤ (s : ℝ) := by positivity
  have htri : |x - (s : ℝ)| ≤ |x| + |(s : ℝ)| := by
    rw [sub_eq_add_neg]
    simpa using (abs_add_le x (-(s : ℝ)))
  have hxabs : |x| = x := abs_of_nonneg hx0
  have hsabs : |(s : ℝ)| = (s : ℝ) := abs_of_nonneg hs0
  have hsle : (s : ℝ) ≤ (n : ℝ) - 1 := by
    have hs' : (s : ℕ) + 1 ≤ n := Nat.succ_le_of_lt hs
    have hsr : ((s : ℕ) + 1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hs'
    linarith
  calc
    |x - (s : ℝ)| ≤ |x| + |(s : ℝ)| := htri
    _ = x + (s : ℝ) := by rw [hxabs, hsabs]
    _ ≤ bSerre + ((n : ℝ) - 1) := by linarith
    _ = bSerre + (n : ℝ) - 1 := by ring
    _ ≤ bSerre + (n : ℝ) := by linarith

end Submission.SqfStage2
