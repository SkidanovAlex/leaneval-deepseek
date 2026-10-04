import Mathlib
import Submission.Work.Diff.STE.flat.inv_jet_bound
import Submission.Work.Diff.STE.flat.level_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.STE.flat.CSq_symInvC_le`

Uniform `H^k` bounds on the Fourier coefficients of the **symmetrised inverse metric**

`symInvC c a b = (2)⁻¹ • (G_{ab} + G_{ba})`,  `G = (reMat (seriesFunM c ·))⁻¹`,

under the two hypotheses that govern the whole flat a priori estimate:

* the level-`k` energy bound `ENormSqFull k (seriesFunM c) ≤ B²`, and
* uniform ellipticity of `reMat (seriesFunM c x)` with constant `lam > 0`.

## Where the statement comes from

The symmetrised inverse metric is the principal coefficient of the flat DeTurck operator
(`level_defs.lean`, `secOpFlat_eq_symInvR`).  The energy estimate of the flat Galerkin system
needs to know that `symInvC c a b`, *as a function on the torus*, has bounded `H^k` norm, with a
bound uniform in the truncation order `N` and in the coefficient family `c`.

## The proof

The inverse-matrix entry `entryVec c x ↦ ((reMatZ ·)⁻¹) c' d'` is a **smooth function of the entry
vector** on the open set `invNonsing n` of non-singular matrices (`invJet_contDiffOn_invPhi`), and
the entry vector of `seriesFunM c` lies in the *compact* elliptic set `invElliptic n lam ρ`
(`invJet_entryVec_mem_elliptic`), which is contained in `invNonsing n` as soon as `lam > 0`
(`invJet_invElliptic_subset_invNonsing`).  Hence the Moser-type composition estimate
`CSq_comp_vecarg_le_local` applies to the *symmetrised* map

`symInvPhi a b z = (2)⁻¹ • (invPhi n a b z + invPhi n b a z)`

with `ρ = s = k`.  The hypothesis `Fintype.card ι < 2 * ρ` of that lemma is `n < 2k`, which follows
from `sob n ≤ k` because `n < 2 * sob n` (`n_lt_two_sob`).  It bounds
`CSq k (fourierCoeff (symInvPhi a b ∘ entryVec c))` by
`C * (1 + Σ_i CSq k (fun m => invCvec n c m i))`; the sum is the level-`k` mass of the entries of
`c`, which `invJet_CSq_entry_le_uniform` dominates by `M * (Ce * ENormSqFull k (seriesFunM c))` with
`M = card (Fin n × Fin n)`, and this is at most `M * (Ce * B²) = Bc²` by the energy hypothesis.

The only remaining point is that the Moser constant depends on the index pair `(a,b)`; taking the
supremum over the (finite, nonempty) index set `Fin n × Fin n` gives a single constant `C` that
works for all `a b`.  The identification `symInvPhi a b (entryVec c x) = symInvC c a b x` is
`symInvPhi_entryVec`.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open MeasureTheory BigOperators

noncomputable section

/-! ## The symmetrised inverse as a function of the entry vector -/

/-- The symmetrised inverse-metric entry as a smooth function of the *entry vector* (the `n²`
complex numbers out of which the real matrix `reMatZ z` is assembled).  Composing it with
`entryVec` recovers `symInvC` (`symInvPhi_entryVec`). -/
def symInvPhi {n : ℕ} (a b : Fin n) :
    (Fin (Fintype.card (Fin n × Fin n)) → ℂ) → ℂ :=
  fun z => (2 : ℂ)⁻¹ • (invPhi n a b z + invPhi n b a z)

/-- `symInvPhi a b` is smooth on the non-singular locus (it is a constant multiple of a sum of two
inverse-matrix entries, `invJet_contDiffOn_invPhi`). -/
lemma contDiffOn_symInvPhi {n : ℕ} (a b : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (symInvPhi a b) (invNonsing n) :=
  ContDiffOn.const_smul ((2 : ℂ)⁻¹)
    ((invJet_contDiffOn_invPhi a b).add (invJet_contDiffOn_invPhi b a))

/-- **Composing the symmetrised inverse entry with the entry vector gives `symInvC`.** -/
lemma symInvPhi_entryVec {n : ℕ} (c : (Fin n → ℤ) → MatC n) (a b : Fin n) :
    (fun x : Fin n → ℝ => symInvPhi a b (entryVec n c x)) = fun x => symInvC c a b x := by
  funext x
  show (2 : ℂ)⁻¹ • (invPhi n a b (fun i => Work.Diff.STE.seriesFun (fun k => invCvec n c k i) x)
        + invPhi n b a (fun i => Work.Diff.STE.seriesFun (fun k => invCvec n c k i) x))
      = ((symInvR c a b x : ℝ) : ℂ)
  rw [invPhi_invCvec c a b x, invPhi_invCvec c b a x, symInvR_apply]
  simp only [smul_eq_mul]
  push_cast
  ring

/-! ## Two elementary sums on the coefficient side -/

/-- **Moment summability of the entry vector of a box-supported family.**  If `c` is supported in
the box `box n N`, so is `fun i => invCvec n c k i`, hence every polynomial moment of that family is
summable. -/
lemma summable_moment_invCvec {n N : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) (M : ℕ) :
    Summable (fun k : Fin n → ℤ => (wt k) ^ M *
      ‖(fun i : Fin (Fintype.card (Fin n × Fin n)) => invCvec n c k i)‖) := by
  refine summable_of_ne_finset_zero (s := box n N) (fun k hk => ?_)
  have hz : (fun i : Fin (Fintype.card (Fin n × Fin n)) => invCvec n c k i) = 0 := by
    funext i
    rw [invCvec_apply, hc k hk]
    simp
  rw [hz]
  simp

/-- **Reindexing the entry-vector sum into the double sum over matrix entries.**  If every entry
family obeys `CSq s (fun m => c m i j) ≤ Ce * E`, then the level-`s` mass of the entry vector is
bounded by `(card) * (Ce * E)`. -/
lemma sum_CSq_invCvec_le {n s : ℕ} (c : (Fin n → ℤ) → MatC n) {Ce E : ℝ}
    (hEntry : ∀ i j : Fin n, CSq s (fun m => c m i j) ≤ Ce * E) :
    (∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq s (fun m => invCvec n c m i)) ≤
      (Fintype.card (Fin n × Fin n) : ℝ) * (Ce * E) := by
  have hstep : (∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq s (fun m => invCvec n c m i))
      = ∑ p : Fin n × Fin n, CSq s (fun m => c m p.1 p.2) :=
    (Fintype.sum_equiv (invEv n) (fun p : Fin n × Fin n => CSq s (fun m => c m p.1 p.2))
      (fun i : Fin (Fintype.card (Fin n × Fin n)) => CSq s (fun m => invCvec n c m i))
      (fun p => by simp only [invCvec_apply, Equiv.symm_apply_apply])).symm
  calc (∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq s (fun m => invCvec n c m i))
      = ∑ p : Fin n × Fin n, CSq s (fun m => c m p.1 p.2) := hstep
    _ ≤ ∑ _p : Fin n × Fin n, (Ce * E) := Finset.sum_le_sum (fun p _ => hEntry p.1 p.2)
    _ = (Fintype.card (Fin n × Fin n) : ℝ) * (Ce * E) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## The target -/

theorem CSq_symInvC_le {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (hk : Work.Diff.STE.flat.sob n ≤ k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
        Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) ≤ B ^ 2 →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
        ∀ a b : Fin n,
          Work.Diff.STE.CSq k
            (Work.Diff.STE.fourierCoeff (fun y => Work.Diff.STE.flat.symInvC c a b y)) ≤ C := by
  classical
  -- the uniform bound on the level-`k` masses of the individual entries
  obtain ⟨Ce, hCe, hCe'⟩ := invJet_CSq_entry_le_uniform (n := n) k
  -- the elliptic radius containing the entry vector
  obtain ⟨ρ, hρnn, hρmem⟩ := invJet_entryVec_mem_elliptic (n := n) (s := k) (Bs := B) hB hk
  set M : ℝ := (Fintype.card (Fin n × Fin n) : ℝ) with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  -- the threshold against which the Moser estimate is applied
  set Bc : ℝ := Real.sqrt (M * Ce) * B with hBcdef
  have hBcnn : 0 ≤ Bc := by rw [hBcdef]; positivity
  -- `sob n ≤ k` implies the Sobolev hypothesis `n < 2k` of the Moser estimate
  have hcard : Fintype.card (Fin n) < 2 * k := by
    rw [Fintype.card_fin]
    exact lt_of_lt_of_le (n_lt_two_sob n) (Nat.mul_le_mul_left 2 hk)
  -- the Moser estimate, one constant per index pair
  have hcmp : ∀ ab : Fin n × Fin n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : (Fin n → ℤ) → (Fin (Fintype.card (Fin n × Fin n)) → ℂ)),
        (∀ N' : ℕ, Summable (fun kk : Fin n → ℤ => (wt kk) ^ N' * ‖c kk‖)) →
        (∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq k (fun kk => c kk i)) ≤ Bc ^ 2 →
        (∀ x : Fin n → ℝ, (fun i => seriesFun (fun kk => c kk i) x) ∈ invElliptic n lam ρ) →
        CSq k (fourierCoeff (fun x => symInvPhi ab.1 ab.2
            (fun i => seriesFun (fun kk => c kk i) x)))
          ≤ C * (1 + ∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq k (fun kk => c kk i)) := by
    intro ab
    exact CSq_comp_vecarg_le_local (ι := Fin n) (m := Fintype.card (Fin n × Fin n)) k k
      hcard le_rfl (symInvPhi ab.1 ab.2) (invNonsing n) invJet_isOpen_invNonsing
      (contDiffOn_symInvPhi ab.1 ab.2) (invElliptic n lam ρ)
      (invJet_isCompact_invElliptic lam ρ) (invJet_invElliptic_subset_invNonsing hlam) Bc hBcnn
  choose Cf hCf using hcmp
  -- the supremum of the Moser constants over the index pairs
  set Cfin : ℝ := Finset.sup' Finset.univ
      ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩ Cf with hCfindef
  have hCfin0 : 0 ≤ Cfin := by
    rw [hCfindef]
    exact le_trans (hCf (⟨0, hn⟩, ⟨0, hn⟩)).1
      (Finset.le_sup' (f := Cf) (Finset.mem_univ _))
  have hCfinle : ∀ ab : Fin n × Fin n, Cf ab ≤ Cfin := by
    intro ab
    rw [hCfindef]
    exact Finset.le_sup' (f := Cf) (Finset.mem_univ ab)
  refine ⟨Cfin * (1 + Bc ^ 2), by positivity, ?_⟩
  intro N c₀ hc hen hell a b
  -- moment summability of the entry vector
  have hmom : ∀ N' : ℕ, Summable (fun kk : Fin n → ℤ => (wt kk) ^ N' *
      ‖(fun i : Fin (Fintype.card (Fin n × Fin n)) => invCvec n c₀ kk i)‖) :=
    fun N' => summable_moment_invCvec c₀ hc N'
  -- the level-`k` mass of the entry vector, reindexed onto the matrix entries
  have hsum1 : (∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq k (fun m => invCvec n c₀ m i))
      ≤ M * (Ce * ENormSqFull k (seriesFunM c₀)) := by
    rw [hMdef]
    exact sum_CSq_invCvec_le c₀ (fun i j => hCe' N c₀ hc i j)
  have hCSqbar : (∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq k (fun m => invCvec n c₀ m i))
      ≤ Bc ^ 2 := by
    refine hsum1.trans ?_
    have h1 : M * (Ce * ENormSqFull k (seriesFunM c₀)) ≤ M * (Ce * B ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hen hCe) hMnn
    refine h1.trans ?_
    rw [hBcdef]
    have heq : (Real.sqrt (M * Ce) * B) ^ 2 = M * (Ce * B ^ 2) := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hMnn hCe)]
      ring
    rw [heq]
  -- membership of the entry vector in the elliptic set
  have hKc : ∀ x : Fin n → ℝ,
      (fun i => seriesFun (fun kk => invCvec n c₀ kk i) x) ∈ invElliptic n lam ρ :=
    fun x => hρmem N c₀ hc hen hell x
  have hmain := (hCf (a, b)).2 (fun kk i => invCvec n c₀ kk i) hmom hCSqbar hKc
  -- identify the composed function with the symmetrised inverse metric
  have hfun : (fun x : Fin n → ℝ => symInvPhi a b
        (fun i => seriesFun (fun kk => (fun kk i => invCvec n c₀ kk i) kk i) x))
      = fun x => symInvC c₀ a b x := symInvPhi_entryVec c₀ a b
  rw [hfun] at hmain
  refine hmain.trans ?_
  have hsum2 : (∑ i : Fin (Fintype.card (Fin n × Fin n)),
      CSq k (fun kk => (fun kk i => invCvec n c₀ kk i) kk i)) ≤ Bc ^ 2 := hCSqbar
  calc Cf (a, b) * (1 + ∑ i : Fin (Fintype.card (Fin n × Fin n)),
          CSq k (fun kk => (fun kk i => invCvec n c₀ kk i) kk i))
      ≤ Cf (a, b) * (1 + Bc ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith [hsum2]) (hCf (a, b)).1
    _ ≤ Cfin * (1 + Bc ^ 2) :=
        mul_le_mul_of_nonneg_right (hCfinle (a, b)) (by positivity)

end

end Work.Diff.STE.flat
