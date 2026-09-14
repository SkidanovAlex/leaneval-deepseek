import ChallengeDeps
import Submission.Vdw.PrimitiveCase
import Submission.Vdw.ImprimitiveInput
import Submission.Vdw.PerFieldFibreAll
import Submission.Vdw.SchmidtCount
import Submission.Commons.NumberTheory.Polynomial.mapMahlerMeasure_int_le
import Submission.Commons.Analysis.Asymptotics.isBigO_of_eventually_le
import Submission.Commons.GroupTheory.GroupAction.ncard_orbit_mul_ncard_of_isBlock

open Polynomial Filter Asymptotics
open scoped BigOperators
open scoped Pointwise
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false

/-!
# The imprimitive slice, sliced by the block system `(k, m)`

`PrimitiveCase.ImprimitiveBad n H` is the set of irreducible bad degree-`n`
polynomials whose Galois group (acting on the roots) is imprimitive.  Its
bound `= O(H^(n-1))` is the last missing input of `theorem_1` for composite
`n ≥ 6` (Widmer's bound `O(H^(n/2+2))`).

This module *slices* that bound by the **block system**: for
`f ∈ ImprimitiveBad n H` one extracts a nontrivial block `B` of the natural
action of `Gal (f.map φℚ)` on the `n` roots (`Fin n`, `n = natDegree`); the
blocks of the system containing `B` are the translates of `B`, so with
`k := B.ncard` (the **block size**) and `m := (orbit of B).ncard` (the **number
of blocks**) one has `k * m = n` and `2 ≤ k, 2 ≤ m`.

## The literature input, sliced

Widmer's theorem (`PerFieldFibre.lean` / `ImprimitiveInput.lean`) bounds the
whole imprimitive slice by `O(H^(n/2+2))`.  Its proof actually proceeds
*per-divisor*: the number of degree-`n` monic irreducible polynomials of
height `≤ H` whose field `K_f` contains a subfield of degree `m` (equivalently:
which admit a block system with `m` blocks of size `k = n/m`) is
`O(H^(k+m))`.  This is the statement recorded below as `ImprimitiveBlockBound`
(the exponent `k + m` is Widmer's `n + e` with `n = k`, `e = m`).

## The block-polynomial route to `ImprimitiveBlockBound`

If the blocks have size `k` and there are `m = n/k` of them, let
`P_j = ∏_{i ∈ B_j} (X - α_i)` be the monic degree-`k` polynomial whose roots
are the elements of the `j`-th block.  Then

* `f = ∏_{j=1}^m P_j` (the roots are partitioned by the blocks);
* the multiset `{P_j}` is stable under the Galois action, and the field of
  definition `L_1 = ℚ(coeffs of P_1)` has degree `m` over `ℚ`;
* the **Mahler measure is multiplicative**: `M(f) = ∏_j M(P_j)`, with every
  factor `≥ 1` (so in particular each `M(P_j) ≤ M(f)`).

Hence `#(k,m)-slice ≤ #{P_1}`, and `P_1` is a point of the `k`-dimensional
`L_1`-space of monic degree-`k` polynomials in the multiplicative region
`∏_j M(P_1^{σ_j}) ≤ Y`; the lattice-point count in that region is
`≍ Y^k (log Y)^(m-1) / |Disc L_1|^(k/2)`, and summing over the possible `L_1`
(with the truncation `|Disc L_1| ≤ Y^(2m-2)` coming from the coefficient bound)
gives the exponent `max{k,m} ≤ k + m`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## Blocks of the natural Galois action -/

/-- **`f` admits a block of size `k`** for the natural action of
`Gal (f.map φℚ)` on the `n` roots (`Fin n`, `n = natDegree (f.map φℚ)`). -/
def HasBlockSize (f : ℤ[X]) (h : Irreducible (f.map φℚ)) (k : ℕ) : Prop :=
  letI : Fact (Irreducible (f.map φℚ)) := ⟨h⟩
  ∃ B : Set (Fin ((f.map φℚ).natDegree)),
    MulAction.IsBlock (irrGalFinHom f).range B ∧ B.ncard = k

/-- **The block extraction.**  An imprimitive irreducible bad polynomial
admits a nontrivial block `B`; with `k = B.ncard` the block size and `m` the
number of blocks (the cardinality of the translate orbit) one has
`2 ≤ k`, `2 ≤ m` and `k * m = n`. -/
theorem imprimitiveBad_has_block (n H : ℕ) (hn : 3 ≤ n) {f : ℤ[X]}
    (hf : f ∈ ImprimitiveBad n H) :
    ∃ (h : Irreducible (f.map φℚ)) (k m : ℕ),
      2 ≤ k ∧ 2 ≤ m ∧ k * m = n ∧ HasBlockSize f h k := by
  classical
  obtain ⟨hbad, hnotprim⟩ := hf
  have hirr : Irreducible (f.map φℚ) := irreducibleBad_mem_irreducible_rat (by omega) hbad
  haveI hFact : Fact (Irreducible (f.map φℚ)) := ⟨hirr⟩
  have hprim : ¬ galPrimitive f hirr := fun hgp => hnotprim ⟨hirr, hgp⟩
  have hnpt : ¬ MulAction.IsPreprimitive (irrGalFinHom f).range
      (Fin ((f.map φℚ).natDegree)) := hprim
  have htrans : MulAction.IsPretransitive (irrGalFinHom f).range
      (Fin ((f.map φℚ).natDegree)) := irrGalFinHom_pretransitive f
  haveI := htrans
  have hblk : ∃ B0 : Set (Fin ((f.map φℚ).natDegree)),
      MulAction.IsBlock (irrGalFinHom f).range B0 ∧ ¬ B0.Subsingleton ∧ B0 ≠ Set.univ := by
    by_contra hcon
    have hall : ∀ B0 : Set (Fin ((f.map φℚ).natDegree)),
        MulAction.IsBlock (irrGalFinHom f).range B0 → MulAction.IsTrivialBlock B0 := by
      intro B0 hB0
      by_contra hnt
      exact hcon ⟨B0, hB0, fun h => hnt (Or.inl h), fun h => hnt (Or.inr h)⟩
    haveI hne : Nonempty (Fin ((f.map φℚ).natDegree)) := by
      refine ⟨⟨0, ?_⟩⟩
      have hdeg : f.degree = n :=
        (Bad_subset_Box n H (irreducibleBad_subset_Bad n H hbad)).2.1
      have hmon : f.Monic := (Bad_subset_Box n H (irreducibleBad_subset_Bad n H hbad)).1
      rw [monic_natDegree_map_rat f hmon, Polynomial.natDegree_eq_of_degree_eq_some hdeg]
      omega
    refine hnpt (MulAction.IsPreprimitive.of_isTrivialBlock_base (Classical.arbitrary _) ?_)
    intro B0 _ hB0
    exact hall B0 hB0
  obtain ⟨B, hBblock, hBns, hBne⟩ := hblk
  let N : ℕ := (f.map φℚ).natDegree
  have hNn : N = n := by
    show (f.map φℚ).natDegree = n
    have hdeg : f.degree = n :=
      (Bad_subset_Box n H (irreducibleBad_subset_Bad n H hbad)).2.1
    have hmon : f.Monic := (Bad_subset_Box n H (irreducibleBad_subset_Bad n H hbad)).1
    rw [monic_natDegree_map_rat f hmon, Polynomial.natDegree_eq_of_degree_eq_some hdeg]
  have hBnon : B.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    exact hBns (by rw [hempty]; exact Set.subsingleton_empty)
  have hk2 : 2 ≤ B.ncard := by
    by_contra hlt
    push Not at hlt
    exact hBns ((B.ncard_le_one_iff_subsingleton).mp (by omega))
  have hkm : B.ncard * (MulAction.orbit (irrGalFinHom f).range B).ncard = n := by
    have h := Commons.GroupTheory.GroupAction.ncard_orbit_mul_ncard_of_isBlock
      htrans hBblock hBnon
    rw [Nat.card_fin, mul_comm] at h
    exact h.trans hNn
  have hm2 : 2 ≤ (MulAction.orbit (irrGalFinHom f).range B).ncard := by
    have hx : ∃ x : Fin N, x ∉ B := by
      by_contra hcon
      push Not at hcon
      exact hBne (Set.eq_univ_iff_forall.mpr hcon)
    obtain ⟨x, hx⟩ := hx
    obtain ⟨b, hb⟩ := hBnon
    obtain ⟨g, hg⟩ := htrans.exists_smul_eq b x
    have hne : g • B ≠ B := by
      intro hcon
      have hmem : x ∈ g • B := Set.mem_smul_set.mpr ⟨b, hb, hg⟩
      rw [hcon] at hmem
      exact hx hmem
    have hsub : ({B, g • B} : Set (Set (Fin N))) ⊆
        MulAction.orbit (irrGalFinHom f).range B := by
      intro C hC
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
      rcases hC with hC | hC
      · rw [hC]; exact MulAction.mem_orbit_self B
      · rw [hC]; exact ⟨g, rfl⟩
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hne.symm] at h2
    exact h2
  exact ⟨hirr, B.ncard, (MulAction.orbit (irrGalFinHom f).range B).ncard, hk2, hm2, hkm,
    B, hBblock, rfl⟩


/-! ## A finite-index union bound for `Set.ncard` -/

/-- The cardinality of a finite union is at most the sum of the cardinalities. -/
lemma ncard_biUnion_le {ι α : Type*} (I : Finset ι) (S : ι → Set α) :
    (⋃ i ∈ I, S i).ncard ≤ ∑ i ∈ I, (S i).ncard := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
      have hsplit : (⋃ i ∈ insert a I, S i) = S a ∪ ⋃ i ∈ I, S i := by
        ext x
        simp only [Finset.mem_insert, Set.mem_iUnion, Set.mem_union]
        constructor
        · rintro ⟨i, rfl | hi, hx⟩
          · exact Or.inl hx
          · exact Or.inr ⟨i, hi, hx⟩
        · rintro (hx | ⟨i, hi, hx⟩)
          · exact ⟨a, Or.inl rfl, hx⟩
          · exact ⟨i, Or.inr hi, hx⟩
      rw [hsplit, Finset.sum_insert ha]
      calc (S a ∪ ⋃ i ∈ I, S i).ncard ≤ (S a).ncard + (⋃ i ∈ I, S i).ncard :=
            Set.ncard_union_le _ _
        _ ≤ (S a).ncard + ∑ i ∈ I, (S i).ncard := by omega

/-! ## The per-block-system counting input -/

/-- **The per-block-system counting input** (Widmer's theorem in sliced form):
the number of box polynomials of degree `k * m` (monic, irreducible,
coefficients bounded by `H`) admitting a block of size `k` — equivalently,
imprimitive with a system of `m` blocks of size `k` — is `O(H^(k + m))`
uniformly in `H`.

The exponent `k + m` is Widmer's `n + e` with `n = k` (the relative degree)
and `e = m` (the degree of the subfield).  The block-polynomial route proves
this with the smaller exponent `max{k,m}`: writing `P_j` for the monic
degree-`k` polynomial whose roots are the elements of the `j`-th block, one
has `f = ∏_j P_j`, the multiset `{P_j}` is Galois stable with field of
definition of degree `m`, and `M(f) = ∏_j M(P_j)` with every factor `≥ 1`. -/
def ImprimitiveBlockBound : Prop :=
  ∀ k m : ℕ, 2 ≤ k → 2 ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ,
    ((({f : ℤ[X] | f ∈ Box (k * m) H ∧ Irreducible (f.map φℚ) ∧
        ∃ h : Irreducible (f.map φℚ), HasBlockSize f h k} : Set ℤ[X]).ncard) : ℝ)
      ≤ C * ((((k : ℝ) * (m : ℝ)) + 1) * ((H : ℝ) + 1)) ^ (k + m)

/-- The finite set of block systems of a degree-`n` imprimitive polynomial: the
pairs (block size, number of blocks). -/
def blockPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun p => 2 ≤ p.1 ∧ 2 ≤ p.2 ∧ p.1 * p.2 = n)

lemma mem_blockPairs {n k m : ℕ} (hk : 2 ≤ k) (hm : 2 ≤ m) (hkm : k * m = n) :
    (k, m) ∈ blockPairs n := by
  simp only [blockPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  refine ⟨⟨?_, ?_⟩, hk, hm, hkm⟩
  · have h1 : k * 2 ≤ k * m := Nat.mul_le_mul_left k hm
    omega
  · have h1 : 2 * m ≤ k * m := Nat.mul_le_mul_right m hk
    omega

/-- **The imprimitive slice is `O(H^(n/2+2))`** (Widmer's bound) from the
per-block-system count. -/
theorem imprimitiveBad_isBigO_of_blockBound (n : ℕ) (hn : 3 ≤ n)
    (hbb : ImprimitiveBlockBound) :
    (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2)) := by
  classical
  let C : ℕ × ℕ → ℝ := fun p =>
    if h : (2 ≤ p.1 ∧ 2 ≤ p.2) then (hbb p.1 p.2 h.1 h.2).choose else 0
  have hC0 : ∀ p, 0 ≤ C p := by
    intro p
    by_cases h : (2 ≤ p.1 ∧ 2 ≤ p.2)
    · dsimp only [C]
      rw [dif_pos h]
      exact (hbb p.1 p.2 h.1 h.2).choose_spec.1
    · dsimp only [C]
      rw [dif_neg h]
  have hCbd : ∀ k m : ℕ, 2 ≤ k → 2 ≤ m → ∀ H : ℕ,
      ((({f : ℤ[X] | f ∈ Box (k * m) H ∧ Irreducible (f.map φℚ) ∧
          ∃ h : Irreducible (f.map φℚ), HasBlockSize f h k} : Set ℤ[X]).ncard) : ℝ)
        ≤ C (k, m) * ((((k : ℝ) * (m : ℝ)) + 1) * ((H : ℝ) + 1)) ^ (k + m) := by
    intro k m h1 h2 H
    dsimp only [C]
    rw [dif_pos ⟨h1, h2⟩]
    exact (hbb k m h1 h2).choose_spec.2 H
  refine IsBigO.of_bound
    ((∑ p ∈ blockPairs n, C p) * (((n : ℝ) + 1) * 2) ^ ((n : ℝ) / 2 + 2)) ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with H hH1
  have hHR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  set Y : ℝ := ((n : ℝ) + 1) * ((H : ℝ) + 1) with hY
  have hY1 : 1 ≤ Y := by
    rw [hY]
    have h0n : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  set T : ℕ × ℕ → Set ℤ[X] := fun p => {f : ℤ[X] | f ∈ ImprimitiveBad n H ∧
      ∃ h : Irreducible (f.map φℚ), HasBlockSize f h p.1} with hT
  have hcover : ImprimitiveBad n H ⊆ ⋃ p ∈ blockPairs n, T p := by
    intro f hf
    obtain ⟨h, k, m, hk2, hm2, hkm, hbk⟩ := imprimitiveBad_has_block n H hn hf
    exact Set.mem_iUnion.mpr ⟨(k, m), Set.mem_iUnion.mpr
      ⟨mem_blockPairs hk2 hm2 hkm, ⟨hf, h, hbk⟩⟩⟩
  have hfin : (⋃ p ∈ blockPairs n, T p).Finite :=
    (box_finite n H).subset fun f hf => by
      simp only [Set.mem_iUnion] at hf
      obtain ⟨p, hp, hfT⟩ := hf
      exact Bad_subset_Box n H (irreducibleBad_subset_Bad n H hfT.1.1)
  have hstep1 : (ImprimitiveBad n H).ncard ≤ ∑ p ∈ blockPairs n, (T p).ncard :=
    (Set.ncard_le_ncard hcover hfin).trans (ncard_biUnion_le _ T)
  have hsub : ∀ p ∈ blockPairs n, T p ⊆
      {f : ℤ[X] | f ∈ Box (p.1 * p.2) H ∧ Irreducible (f.map φℚ) ∧
        ∃ h : Irreducible (f.map φℚ), HasBlockSize f h p.1} := by
    intro p hp f hf
    have hkm : p.1 * p.2 = n := (Finset.mem_filter.mp hp).2.2.2
    exact ⟨by rw [hkm]; exact Bad_subset_Box n H (irreducibleBad_subset_Bad n H hf.1.1),
      irreducibleBad_mem_irreducible_rat (by omega) hf.1.1, hf.2⟩
  have hstep2 : ∀ p ∈ blockPairs n,
      ((T p).ncard : ℝ) ≤ C p * Y ^ ((p.1 : ℝ) + (p.2 : ℝ)) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    obtain ⟨hk2, hm2, hkm⟩ := hp'.2
    have hle : (T p).ncard ≤ ({f : ℤ[X] | f ∈ Box (p.1 * p.2) H ∧
        Irreducible (f.map φℚ) ∧
        ∃ h : Irreducible (f.map φℚ), HasBlockSize f h p.1} : Set ℤ[X]).ncard :=
      Set.ncard_le_ncard (hsub p hp) ((box_finite (p.1 * p.2) H).subset fun f hf => hf.1)
    refine (Nat.cast_le.mpr hle).trans ?_
    have h := hCbd p.1 p.2 hk2 hm2 H
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hC0 p)
    have hbase : (((p.1 : ℝ) * (p.2 : ℝ)) + 1) * ((H : ℝ) + 1) = Y := by
      rw [hY, ← Nat.cast_mul, hkm]
    rw [hbase, ← Real.rpow_natCast Y (p.1 + p.2)]
    push_cast
    rfl
  have hstep3 : ∑ p ∈ blockPairs n, ((T p).ncard : ℝ)
      ≤ ∑ p ∈ blockPairs n, C p * Y ^ ((n : ℝ) / 2 + 2) := by
    refine Finset.sum_le_sum fun p hp => ?_
    refine (hstep2 p hp).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hC0 p)
    have hp' := Finset.mem_filter.mp hp
    obtain ⟨hk2, hm2, hkm⟩ := hp'.2
    have hkR : ((p.1 : ℝ) + (p.2 : ℝ)) ≤ (n : ℝ) / 2 + 2 := by
      have h1 : (2 : ℝ) * ((p.1 : ℝ) + (p.2 : ℝ)) ≤ (n : ℝ) + 4 := by
        have h2 : 2 * (p.1 + p.2) ≤ n + 4 := by
          have := Nat.mul_le_mul hk2 hm2
          rw [hkm] at this
          nlinarith
        exact_mod_cast h2
      linarith
    exact Real.rpow_le_rpow_of_exponent_le hY1 hkR
  have hstep4 : ((∑ p ∈ blockPairs n, (T p).ncard : ℕ) : ℝ)
      = ∑ p ∈ blockPairs n, ((T p).ncard : ℝ) := by
    push_cast
    ring
  have hfinal : ((ImprimitiveBad n H).ncard : ℝ)
      ≤ (∑ p ∈ blockPairs n, C p) * Y ^ ((n : ℝ) / 2 + 2) := by
    calc ((ImprimitiveBad n H).ncard : ℝ)
        ≤ ((∑ p ∈ blockPairs n, (T p).ncard : ℕ) : ℝ) := by exact_mod_cast hstep1
      _ = ∑ p ∈ blockPairs n, ((T p).ncard : ℝ) := hstep4
      _ ≤ (∑ p ∈ blockPairs n, C p) * Y ^ ((n : ℝ) / 2 + 2) := by
          rw [Finset.sum_mul]
          exact hstep3
  have h0 : (0 : ℝ) ≤ ∑ p ∈ blockPairs n, C p := Finset.sum_nonneg fun p hp => hC0 p
  have hkey : Y ≤ (((n : ℝ) + 1) * 2) * (H : ℝ) := by
    rw [hY]
    have h0n : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hY0 : 0 ≤ Y := le_trans (by norm_num) hY1
  have hkey' : Y ^ ((n : ℝ) / 2 + 2) ≤ ((((n : ℝ) + 1) * 2) * (H : ℝ)) ^ ((n : ℝ) / 2 + 2) :=
    Real.rpow_le_rpow hY0 hkey (by positivity)
  have hmain : (∑ p ∈ blockPairs n, C p) * Y ^ ((n : ℝ) / 2 + 2) ≤
      ((∑ p ∈ blockPairs n, C p) * (((n : ℝ) + 1) * 2) ^ ((n : ℝ) / 2 + 2))
        * (H : ℝ) ^ ((n : ℝ) / 2 + 2) := by
    calc (∑ p ∈ blockPairs n, C p) * Y ^ ((n : ℝ) / 2 + 2)
        ≤ (∑ p ∈ blockPairs n, C p) * ((((n : ℝ) + 1) * 2) * (H : ℝ)) ^ ((n : ℝ) / 2 + 2) :=
          mul_le_mul_of_nonneg_left hkey' h0
      _ = ((∑ p ∈ blockPairs n, C p) * (((n : ℝ) + 1) * 2) ^ ((n : ℝ) / 2 + 2))
            * (H : ℝ) ^ ((n : ℝ) / 2 + 2) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
          ring
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact hfinal.trans hmain

/-- **The challenge theorem for composite `n ≥ 6`** from the per-block-system
imprimitive count: van der Waerden's conjecture in degree `n` follows from
`#ImprimitiveBad n H = O(H^(n/2+2))` (which the block-system count supplies)
together with Schmidt's field count (a theorem). -/
theorem theorem_1_of_blockBound (n : ℕ) (hn : 6 ≤ n) (hbb : ImprimitiveBlockBound) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < ((n : ℝ) + 2) / 4 := by
    have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    rw [div_lt_iff₀ hden]
    nlinarith
  exact theorem_1_of_fieldCountBound n (by omega) (((n : ℝ) + 2) / 4) hβ
    (weylM_exponent_schmidt n hn) (fieldCountBound_schmidt n (by omega))
    (ImprimitiveBad_isBigO_of_widmer n hn
      (imprimitiveBad_isBigO_of_blockBound n (by omega) hbb))

end

end Submission.Vdw
