import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.Basic
import Submission.Work.Q44Geom.latW_count
import Submission.Work.Q44Geom.formOf_eval
import Submission.Work.Q44Geom.sat_span
import Submission.Work.Q44Geom.ratSpan_finrank
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.Q44Child.superlattice_basis
import Submission.Work.HP.Q44Child.basis_ext

/-!
# Auxiliary definitions and lemmas for `Work.Q44Geom.bad_count`

This file collects the shared vocabulary and the elementary structural lemmas used to bound
the number of `L ∈ Sset c s` without a good pair.

* `badSet c s`, `badASet c s`, `bad2Set c s` : the bad set and its two pieces according to
  `rk (L ⊓ latW (f44 c))`;
* `Wlat c`, `Nof c L` : the invariance lattice `latW (f44 c)` and the rank-`2` auxiliary
  lattice `L ⊓ Wlat c`;
* `isPrimLat_latW`, `isPrimLat_inf` : `latW f` is saturated and saturated lattices are closed
  under intersection;
* `formOf_totalDegree_le` : `formOf d n a` has total degree at most `d`;
* `latW_count_uniform` : `latW_count` with the constant pulled outside the quantifiers;
* `ratSpan_mono`, `ratSpan_latW_le`, `ratSpan_finrank_general` : elementary properties of the
  `ℚ`-span of a lattice, used to compare ranks without invoking `finrank_mono` over `ℤ`;
* `gen_of_le` : a rank-`3` lattice `L` containing a primitive rank-`2` lattice `N` is generated
  over `N` by a single vector;
* `ncard_mul_le_of_disjoint` : counting over a disjoint family of subsets of a finite set.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Q44Geom

open MvPolynomial

/-! ## The bad set and its two pieces -/

/-- The set of lattices of `Sset c s` admitting *no* good pair. -/
def badSet (c : Work.HP.Mon 4 4 → ℤ) (s : Fin 3 → ℝ) : Set (Submodule ℤ (Fin 5 → ℤ)) :=
  {L | L ∈ Sset c s ∧ ¬ goodPair c s L}

/-- The invariance lattice `W = latW (f44 c)`. -/
def Wlat (c : Work.HP.Mon 4 4 → ℤ) : Submodule ℤ (Fin 5 → ℤ) := latW (f44 c)

/-- The rank-`2` auxiliary lattice `N = L ⊓ latW (f44 c)` attached to `L`. -/
def Nof (c : Work.HP.Mon 4 4 → ℤ) (L : Submodule ℤ (Fin 5 → ℤ)) :
    Submodule ℤ (Fin 5 → ℤ) := L ⊓ Wlat c

/-- The part of the bad set for which `L ⊓ W` has rank `3`. -/
def badASet (c : Work.HP.Mon 4 4 → ℤ) (s : Fin 3 → ℝ) : Set (Submodule ℤ (Fin 5 → ℤ)) :=
  {L | L ∈ badSet c s ∧ Work.HP.rk (L ⊓ Wlat c) = 3}

/-- The part of the bad set for which `L ⊓ W` has rank `2`. -/
def bad2Set (c : Work.HP.Mon 4 4 → ℤ) (s : Fin 3 → ℝ) : Set (Submodule ℤ (Fin 5 → ℤ)) :=
  {L | L ∈ badSet c s ∧ Work.HP.rk (L ⊓ Wlat c) = 2}

/-! ## Primitiveness -/

/-- The integral points of the rational subspace `invSub f` form a saturated (primitive)
sublattice of `ℤ^5`. -/
theorem isPrimLat_latW (f : MvPolynomial (Fin 5) ℚ) : Work.HP.IsPrimLat (latW f) := by
  intro v m hm hmem
  rw [mem_latW_iff] at hmem ⊢
  have h2 : toRatLM (m • v) = (m : ℚ) • toRatLM v := by
    rw [map_smul]
    exact Int.cast_smul_eq_zsmul ℚ m (toRatLM v)
  rw [h2] at hmem
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have h3 := (invSub f).smul_mem ((m : ℚ)⁻¹) hmem
  rwa [smul_smul, inv_mul_cancel₀ hmq, one_smul] at h3

theorem isPrimLat_Wlat (c : Work.HP.Mon 4 4 → ℤ) : Work.HP.IsPrimLat (Wlat c) :=
  isPrimLat_latW (f44 c)

/-- Saturated sublattices are closed under intersection. -/
theorem isPrimLat_inf {N L : Submodule ℤ (Fin 5 → ℤ)} (hN : Work.HP.IsPrimLat N)
    (hL : Work.HP.IsPrimLat L) : Work.HP.IsPrimLat (N ⊓ L) := by
  intro v m hm hmem
  rw [Submodule.mem_inf] at hmem ⊢
  exact ⟨hN v m hm hmem.1, hL v m hm hmem.2⟩

/-! ## Degree and uniform counting for `latW` -/

/-- `formOf d n a` is a polynomial of total degree at most `d`. -/
theorem formOf_totalDegree_le (d n : ℕ) (a : Work.HP.Mon d n → ℤ) :
    (Work.HP.formOf d n a).totalDegree ≤ d := by
  have hsum : ∀ m : Work.HP.Mon d n, (m.toFinsupp.sum fun _ e => e) = d := by
    intro m
    rw [Finsupp.sum_fintype _ _ (fun i => rfl)]
    simpa [Work.HP.Mon_toFinsupp_apply] using m.2
  have hdeg : ∀ m ∈ (Finset.univ : Finset (Work.HP.Mon d n)),
      (MvPolynomial.monomial m.toFinsupp (a m : ℚ)).totalDegree ≤ d := by
    intro m _
    by_cases h0 : a m = 0
    · have h0q : ((a m : ℤ) : ℚ) = 0 := by simp [h0]
      rw [h0q, MvPolynomial.monomial_zero, MvPolynomial.totalDegree_zero]
      exact Nat.zero_le d
    · rw [MvPolynomial.totalDegree_monomial m.toFinsupp (by exact_mod_cast h0)]
      exact le_of_eq (hsum m)
  simpa [Work.HP.formOf] using MvPolynomial.totalDegree_finsetSum_le hdeg

/-- `latW_count` with the constant pulled outside the quantifiers: the bound `#(latW f ∩ B(T))
≤ C (1+T)^3` holds with a constant `C` independent of `f`. -/
theorem latW_count_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : MvPolynomial (Fin 5) ℚ),
      Module.finrank ℚ (invSub f) ≤ 3 → ∀ T : ℝ, 1 ≤ T →
      (({v : Fin 5 → ℤ | v ∈ latW f ∧ Work.HP.eNorm v ≤ T} : Set (Fin 5 → ℤ)).ncard : ℝ)
        ≤ C * (1 + T) ^ 3 := by
  obtain ⟨K, hKpos, hK⟩ := Work.HP.ballCount_le_pow_rk (ι := Fin 5)
  refine ⟨K, hKpos, ?_⟩
  intro f hf T hT1
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have hb := hK (latW f) T hT0
  have hrk : Work.HP.rk (latW f) ≤ 3 := le_trans (latW_rank_le f) hf
  have hball : Work.HP.ballCount (latW f) T
      = ({v : Fin 5 → ℤ | v ∈ latW f ∧ Work.HP.eNorm v ≤ T} : Set (Fin 5 → ℤ)).ncard := rfl
  rw [← hball]
  refine le_trans hb ?_
  have h1 : (1 : ℝ) ≤ T + 1 := by linarith
  have hpow : (T + 1) ^ (Work.HP.rk (latW f)) ≤ (T + 1) ^ 3 := pow_le_pow_right₀ h1 hrk
  calc K * (T + 1) ^ (Work.HP.rk (latW f)) ≤ K * (T + 1) ^ 3 :=
        mul_le_mul_of_nonneg_left hpow hKpos.le
    _ = K * (1 + T) ^ 3 := by rw [add_comm]

/-! ## The rational span of a lattice -/

/-- `ratSpan` is monotone in the lattice. -/
theorem ratSpan_mono {L L' : Submodule ℤ (Fin 5 → ℤ)} (h : L ≤ L') : ratSpan L ≤ ratSpan L' := by
  rw [ratSpan_eq, ratSpan_eq]
  refine Submodule.span_mono ?_
  rintro x ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

/-- The `ℚ`-span of the invariance lattice `latW f` is contained in the invariance subspace. -/
theorem ratSpan_latW_le (f : MvPolynomial (Fin 5) ℚ) : ratSpan (latW f) ≤ invSub f := by
  rw [ratSpan_eq, Submodule.span_le]
  rintro x ⟨v, hv, rfl⟩
  exact mem_latW_iff.mp hv

/-- The `ℚ`-dimension of the rational span of a lattice is its `ℤ`-rank. -/
theorem ratSpan_finrank_general (L : Submodule ℤ (Fin 5 → ℤ)) :
    Module.finrank ℚ (ratSpan L) = Work.HP.rk L := by
  classical
  have hψ : Function.Injective (toRatLM.comp (Submodule.subtype L)) := by
    intro x y hxy
    have h : ∀ i, (((x : Fin 5 → ℤ) i : ℤ) : ℚ) = (((y : Fin 5 → ℤ) i : ℤ) : ℚ) :=
      fun i => congrFun hxy i
    refine Subtype.ext (funext fun i => ?_)
    exact_mod_cast h i
  have hkey := finrank_span_range_eq L (Fin 5 → ℚ) (toRatLM.comp (Submodule.subtype L)) hψ
  have hrat : ratSpan L
      = Submodule.span ℚ (Set.range (toRatLM.comp (Submodule.subtype L))) := rfl
  rw [hrat, hkey]
  rfl

/-! ## A generator of `L` over a primitive rank-`2` sublattice -/

/-- If `N ≤ L` are sublattices of `ℤ^5` with `N` saturated of rank `2` and `L` of rank `3`,
then `L = N + ℤ z` for a single vector `z ∈ L`. -/
theorem gen_of_le (N L : Submodule ℤ (Fin 5 → ℤ)) (hNL : N ≤ L) (hN : Work.HP.IsPrimLat N)
    (hrkN : Work.HP.rk N = 2) (hrkL : Work.HP.rk L = 3) :
    ∃ z : Fin 5 → ℤ, z ∈ L ∧ ∀ w ∈ L, ∃ k : ℤ, ∃ n ∈ N, w = k • z + n := by
  classical
  obtain ⟨b, hb, -, -⟩ := Work.HP.Q44Child.basis_ext N hrkN hN
  have hbase : Work.HP.Q44Child.baseLam b ≤ L := by
    rw [Work.HP.Q44Child.baseLam, ← hb]
    exact hNL
  obtain ⟨v, hvL, hLv⟩ := Work.HP.Q44Child.superlattice_basis b L hbase hrkL
  refine ⟨v, hvL, ?_⟩
  intro w hw
  rw [hLv] at hw
  set A : Fin 5 → ℤ := b (Fin.castLE (by norm_num : 2 ≤ 5) (0 : Fin 2)) with hA
  set B : Fin 5 → ℤ := b (Fin.castLE (by norm_num : 2 ≤ 5) (1 : Fin 2)) with hB
  have hA_mem : A ∈ N := by
    rw [hb]
    exact Submodule.subset_span ⟨(0 : Fin 2), rfl⟩
  have hB_mem : B ∈ N := by
    rw [hb]
    exact Submodule.subset_span ⟨(1 : Fin 2), rfl⟩
  have hsup : Submodule.span ℤ ({A, B, v} : Set (Fin 5 → ℤ)) ≤ N ⊔ Submodule.span ℤ {v} := by
    rw [Submodule.span_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact Submodule.mem_sup_left hA_mem
    · rw [hx]; exact Submodule.mem_sup_left hB_mem
    · rw [hx]
      exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton_iff.mpr rfl))
  obtain ⟨n, hn, u, hu, hnu⟩ := Submodule.mem_sup.mp (hsup hw)
  rw [Submodule.mem_span_singleton] at hu
  obtain ⟨k, rfl⟩ := hu
  exact ⟨k, n, hn, by rw [← hnu]; abel⟩

/-! ## Counting over a disjoint family of subsets -/

/-- If `(t i)_{i ∈ s}` is a family of nonempty pairwise disjoint subsets of a finite set `S`,
each with at least `k` elements, then `#s * k ≤ #S`. -/
theorem ncard_mul_le_of_disjoint {ι α : Type*} (s : Set ι) (t : ι → Set α) (S : Set α) (k : ℝ)
    (hS : S.Finite) (hne : ∀ i ∈ s, (t i).Nonempty) (hsub : ∀ i ∈ s, t i ⊆ S)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (t i) (t j))
    (hk : ∀ i ∈ s, k ≤ ((t i).ncard : ℝ)) :
    (s.ncard : ℝ) * k ≤ (S.ncard : ℝ) := by
  classical
  haveI hSft : Fintype S := hS.fintype
  -- `s` is finite, since `i ↦` a chosen element of `t i` is injective into `S`.
  have hsf : s.Finite := by
    choose g hg using hne
    have hinj : Function.Injective (fun i : s => (⟨g i.1 i.2, hsub i.1 i.2 (hg i.1 i.2)⟩ : S)) := by
      intro i j hij
      have h2 : g i.1 i.2 = g j.1 j.2 := congrArg Subtype.val hij
      by_contra hne'
      have hne2 : i.1 ≠ j.1 := fun h => hne' (Subtype.ext h)
      have hd := Set.disjoint_left.mp (hdisj i.1 i.2 j.1 j.2 hne2)
      exact hd (hg i.1 i.2) (h2 ▸ hg j.1 j.2)
    haveI : Fintype s := Fintype.ofInjective _ hinj
    exact Set.toFinite s
  have hpd : s.PairwiseDisjoint t := fun i hi j hj hij => hdisj i hi j hj hij
  have hEq : (⋃ i ∈ s, t i).ncard = ∑ i ∈ hsf.toFinset, (t i).ncard := by
    rw [hsf.ncard_biUnion (fun i hi => hS.subset (hsub i hi)) hpd,
      finsum_mem_eq_finite_toFinset_sum _ hsf]
  have hle : (⋃ i ∈ s, t i).ncard ≤ S.ncard := by
    refine Set.ncard_le_ncard ?_ hS
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact hsub i hi hxi
  have hsum : (∑ i ∈ hsf.toFinset, (t i).ncard) ≤ S.ncard := by
    rw [← hEq]; exact hle
  have hmul : (hsf.toFinset.card : ℝ) * k ≤ ∑ i ∈ hsf.toFinset, ((t i).ncard : ℝ) := by
    calc (hsf.toFinset.card : ℝ) * k = ∑ _i ∈ hsf.toFinset, k := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ hsf.toFinset, ((t i).ncard : ℝ) :=
          Finset.sum_le_sum fun i hi => hk i (hsf.mem_toFinset.mp hi)
  have hcast : ((∑ i ∈ hsf.toFinset, (t i).ncard : ℕ) : ℝ)
      = ∑ i ∈ hsf.toFinset, ((t i).ncard : ℝ) := by
    push_cast
    rfl
  calc (s.ncard : ℝ) * k = (hsf.toFinset.card : ℝ) * k := by
        rw [Set.ncard_eq_toFinset_card s hsf]
    _ ≤ ∑ i ∈ hsf.toFinset, ((t i).ncard : ℝ) := hmul
    _ = ((∑ i ∈ hsf.toFinset, (t i).ncard : ℕ) : ℝ) := hcast.symm
    _ ≤ (S.ncard : ℝ) := by exact_mod_cast hsum

/-- A bad lattice contains two independent vectors of `L ⊓ W` of norm at most `s 0` and `s 1`.

This is `bad_structure` together with the norm bounds of `exists_pair_short`: since `L` has no
good pair, the two short vectors of `L` supplied by `exists_pair_short` must both be invariance
directions, hence lie in `Nof c L = L ⊓ Wlat c`. -/
lemma short_pair_in_Nof {c : Work.HP.Mon 4 4 → ℤ} {s : Fin 3 → ℝ}
    {L : Submodule ℤ (Fin 5 → ℤ)} (hL : L ∈ Sset c s) (hbad : ¬ goodPair c s L) :
    ∃ x y : Fin 5 → ℤ, x ∈ L ⊓ Wlat c ∧ y ∈ L ⊓ Wlat c ∧ LinearIndependent ℤ ![x, y] ∧
      Work.HP.eNorm x ≤ s 0 ∧ Work.HP.eNorm y ≤ s 1 := by
  obtain ⟨hprim, hLrk, hs, hv⟩ := hL
  obtain ⟨b₁, b₂, hb₁, hb₂, hind, hn₁, hn₂⟩ := exists_pair_short L hLrk s hs
  by_cases h₁ : toRatLM b₁ ∈ invSub (f44 c)
  · by_cases h₂ : toRatLM b₂ ∈ invSub (f44 c)
    · exact ⟨b₁, b₂, Submodule.mem_inf.mpr ⟨hb₁, mem_latW_iff.mpr h₁⟩,
        Submodule.mem_inf.mpr ⟨hb₂, mem_latW_iff.mpr h₂⟩, hind, hn₁, hn₂⟩
    · exact absurd ⟨b₁, b₂, hb₁, hb₂, hind, hn₁, hn₂, Or.inr h₂⟩ hbad
  · exact absurd ⟨b₁, b₂, hb₁, hb₂, hind, hn₁, hn₂, Or.inl h₁⟩ hbad

/-- Two linearly independent vectors of a submodule of `ℤ^5` force rank at least `2`. -/
lemma two_le_rk_of_linIndep {N : Submodule ℤ (Fin 5 → ℤ)} {x y : Fin 5 → ℤ}
    (hx : x ∈ N) (hy : y ∈ N) (h : LinearIndependent ℤ ![x, y]) : 2 ≤ Work.HP.rk N := by
  have hv : ∀ i : Fin 2, (![x, y] i) ∈ N := by
    intro i
    fin_cases i
    · simpa using hx
    · simpa using hy
  let v : Fin 2 → N := fun i => ⟨![x, y] i, hv i⟩
  have hli : LinearIndependent ℤ v := by
    refine LinearIndependent.of_comp N.subtype ?_
    have hcomp : ⇑N.subtype ∘ v = ![x, y] := by funext i; rfl
    rw [hcomp]; exact h
  have h2 := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h2
  exact h2

end Work.Q44Geom
