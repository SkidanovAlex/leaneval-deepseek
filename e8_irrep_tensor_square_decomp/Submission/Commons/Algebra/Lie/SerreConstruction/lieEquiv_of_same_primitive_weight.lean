import Mathlib
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_zero_weightSpace_finrank
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_weightSpace_reflect_finrank
import Submission.Commons.Algebra.Lie.SerreConstruction.lieSpan_range_generators
import Submission.Commons.Algebra.Lie.SerreConstruction.eq_top_of_lieSubalgebra_of_generators
import Submission.Commons.Algebra.Lie.TriangularSpan.span_triMon_eq_top
import Submission.Commons.LinearAlgebra.Matrix.Cartan.exists_w_mul_E8
import Submission.Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open CartanMatrix

namespace Commons.Algebra.Lie.SerreConstruction

open UniversalEnvelopingAlgebra

/-!
# Two irreducible `e₈`-modules with the same primitive weight are isomorphic

This is the uniqueness of highest-weight modules, proved without any finite-dimensionality or
Verma-module theory: if `M`, `M'` are irreducible `L8`-modules and `x ∈ M`, `x' ∈ M'` are non-zero
vectors that are killed by all the raising operators `SerreE i` and are eigenvectors of the Cartan
generators `SerreH i` with the *same* weight `ν`, then `M ≃ M'`.

The proof is the classical "diagonal submodule" argument.  In `P = M × M'` consider the submodule
`N = U(e₈)·(x, x')`.  Adapting the triangular spanning theorem
(`Commons.Algebra.Lie.TriangularSpan.span_triMon_eq_top`) shows that `N` is spanned by the word
vectors `F_{i₁}⋯F_{i_k}·(x,x')`; using the height operator `𝔥 = ∑ wⱼ·ad(Hⱼ)` (with `∑ wⱼ Aⱼᵢ = 1`,
`Commons.LinearAlgebra.Matrix.Cartan.exists_w_mul_E8`) one sees that the operator
`∏_{k=1}^m (𝔥 - (𝔥₀ - k))` annihilates every word vector of length `k > 0` but not `(x,x')`.
Consequently the sum of two proper submodules of `N` is proper: `N` has a unique maximal submodule.
Both projections `N → M` and `N → M'` are surjective with maximal kernels, so these kernels
coincide, hence are trivial; the two projections are therefore isomorphisms.
-/

/-- The product of two `L8`-modules, with the componentwise Lie action. -/
private instance prodLieRingModule {M M' : Type*} [AddCommGroup M] [LieRingModule L8 M]
    [AddCommGroup M'] [LieRingModule L8 M'] : LieRingModule L8 (M × M') where
  bracket x p := (⁅x, p.1⁆, ⁅x, p.2⁆)
  add_lie x y p := by
    show (⁅x + y, p.1⁆, ⁅x + y, p.2⁆) = (⁅x, p.1⁆, ⁅x, p.2⁆) + (⁅y, p.1⁆, ⁅y, p.2⁆)
    rw [add_lie, add_lie]; rfl
  lie_add x p q := by
    show (⁅x, p.1 + q.1⁆, ⁅x, p.2 + q.2⁆) = (⁅x, p.1⁆, ⁅x, p.2⁆) + (⁅x, q.1⁆, ⁅x, q.2⁆)
    rw [lie_add, lie_add]; rfl
  leibniz_lie x y p := by
    show (⁅x, ⁅y, p.1⁆⁆, ⁅x, ⁅y, p.2⁆⁆)
      = (⁅⁅x, y⁆, p.1⁆, ⁅⁅x, y⁆, p.2⁆) + (⁅y, ⁅x, p.1⁆⁆, ⁅y, ⁅x, p.2⁆⁆)
    rw [leibniz_lie x y p.1, leibniz_lie x y p.2]; rfl

/-- The product of two `L8`-modules, with the componentwise Lie action. -/
private instance prodLieModule {M M' : Type*} [AddCommGroup M] [Module ℂ M] [LieRingModule L8 M]
    [LieModule ℂ L8 M] [AddCommGroup M'] [Module ℂ M'] [LieRingModule L8 M']
    [LieModule ℂ L8 M'] : LieModule ℂ L8 (M × M') where
  smul_lie t x p := by
    show (⁅t • x, p.1⁆, ⁅t • x, p.2⁆) = t • (⁅x, p.1⁆, ⁅x, p.2⁆)
    rw [smul_lie, smul_lie, Prod.smul_mk]
  lie_smul t x p := by
    show (⁅x, (t • p).1⁆, ⁅x, (t • p).2⁆) = t • (⁅x, p.1⁆, ⁅x, p.2⁆)
    rw [Prod.smul_fst, Prod.smul_snd, lie_smul, lie_smul, Prod.smul_mk]

section General

variable {P : Type*} [AddCommGroup P] [Module ℂ P] [LieRingModule L8 P] [LieModule ℂ L8 P]

/-- The action of the enveloping algebra on a Lie module, as a `ℂ`-algebra homomorphism. -/
noncomputable def uAct : UniversalEnvelopingAlgebra ℂ L8 →ₐ[ℂ] Module.End ℂ P :=
  UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ L8 P)

lemma uAct_iota (x : L8) (p : P) : uAct (UniversalEnvelopingAlgebra.ι ℂ x) p = ⁅x, p⁆ := by
  rw [uAct, UniversalEnvelopingAlgebra.lift_ι_apply, LieModule.toEnd_apply_apply]

lemma uAct_mul (u v : UniversalEnvelopingAlgebra ℂ L8) (p : P) :
    uAct (u * v) p = uAct u (uAct v p) := by rw [map_mul]; rfl

lemma uAct_one (p : P) : uAct (1 : UniversalEnvelopingAlgebra ℂ L8) p = p := by rw [map_one]; rfl

lemma uAct_smul (c : ℂ) (u : UniversalEnvelopingAlgebra ℂ L8) (p : P) :
    uAct (c • u) p = c • uAct u p := by rw [map_smul]; rfl

lemma uAct_add (u v : UniversalEnvelopingAlgebra ℂ L8) (p : P) :
    uAct (u + v) p = uAct u p + uAct v p := by rw [map_add]; rfl

lemma uAct_comm (u : UniversalEnvelopingAlgebra ℂ L8) (c : ℂ) (p : P) :
    uAct u (c • p) = c • uAct u p := (uAct u).map_smul c p

/-- The product in `U(e₈)` of the `ι`-images of the letters of a word, in a family. -/
noncomputable def wordU (f : Fin 8 → L8) (w : List (Fin 8)) : UniversalEnvelopingAlgebra ℂ L8 :=
  (w.map (fun i => UniversalEnvelopingAlgebra.ι ℂ (f i))).prod

@[simp] lemma wordU_nil (f : Fin 8 → L8) : wordU f [] = 1 := by simp [wordU]

lemma wordU_cons (f : Fin 8 → L8) (i : Fin 8) (w : List (Fin 8)) :
    wordU f (i :: w) = UniversalEnvelopingAlgebra.ι ℂ (f i) * wordU f w := by simp [wordU]

noncomputable abbrev fword : List (Fin 8) → UniversalEnvelopingAlgebra ℂ L8 := wordU SerreF
noncomputable abbrev hword : List (Fin 8) → UniversalEnvelopingAlgebra ℂ L8 := wordU SerreH
noncomputable abbrev eword : List (Fin 8) → UniversalEnvelopingAlgebra ℂ L8 := wordU SerreE

@[simp] lemma fword_nil : fword [] = 1 := wordU_nil SerreF
@[simp] lemma hword_nil : hword [] = 1 := wordU_nil SerreH
@[simp] lemma eword_nil : eword [] = 1 := wordU_nil SerreE

/-- The word vector: apply the `F`-monomial of `w` to `z`. -/
noncomputable def V (z : P) (w : List (Fin 8)) : P := uAct (fword w) z

@[simp] lemma V_nil (z : P) : V z [] = z := by simp [V]

lemma V_cons (z : P) (i : Fin 8) (w : List (Fin 8)) :
    V z (i :: w) = ⁅SerreF i, V z w⁆ := by
  rw [V, fword, wordU_cons, uAct_mul, V, fword, uAct_iota]

/-- The `H`-weight of a word vector. -/
lemma iotaH_V (z : P) (nu : Fin 8 → ℤ)
    (hzH : ∀ j, ⁅SerreH j, z⁆ = ((nu j : ℤ) : ℂ) • z) (j : Fin 8) (w : List (Fin 8)) :
    ⁅SerreH j, V z w⁆
      = (((nu j : ℤ) : ℂ) - (w.map (fun i => ((E8 j i : ℤ) : ℂ))).sum) • V z w := by
  induction w with
  | nil => simpa using hzH j
  | cons i w ih =>
      rw [V_cons, leibniz_lie, serreLie_H_F_c, smul_lie, ih, lie_smul]
      have hmap : (List.map (fun i => ((E8 j i : ℤ) : ℂ)) (i :: w)).sum
          = ((E8 j i : ℤ) : ℂ) + (List.map (fun i => ((E8 j i : ℤ) : ℂ)) w).sum := by
        rw [List.map_cons, List.sum_cons]
      rw [hmap]
      module

/-- The submodule generated by `z` under the enveloping action. -/
noncomputable def Nsub (z : P) : Submodule ℂ P :=
  Submodule.span ℂ (Set.range fun u : UniversalEnvelopingAlgebra ℂ L8 => uAct u z)

lemma uAct_mem_Nsub (z : P) (u : UniversalEnvelopingAlgebra ℂ L8) : uAct u z ∈ Nsub z :=
  Submodule.subset_span ⟨u, rfl⟩

/-- `Nsub z` as a Lie submodule (it is stable under the Lie action). -/
noncomputable def N (z : P) : LieSubmodule ℂ L8 P :=
  LieSubmodule.mk (Nsub z) (by
    intro x p hp
    refine Submodule.span_induction (p := fun p _ => ⁅x, p⁆ ∈ Nsub z) ?_ ?_ ?_ ?_ hp
    · rintro p ⟨u, rfl⟩
      have : ⁅x, uAct u z⁆ = uAct (UniversalEnvelopingAlgebra.ι ℂ x * u) z := by
        rw [uAct_mul, uAct_iota]
      rw [this]
      exact uAct_mem_Nsub z _
    · rw [lie_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
    · intro c a _ ha; rw [lie_smul]; exact Submodule.smul_mem _ c ha)

lemma self_mem_N (z : P) : z ∈ N z := by
  simpa [N, Nsub] using uAct_mem_Nsub z 1

/-- The enveloping algebra acts on `K`, for any Lie submodule `K`. -/
lemma uAct_mem_of_mem (K : LieSubmodule ℂ L8 P) {y : P} (hy : y ∈ K)
    (u : UniversalEnvelopingAlgebra ℂ L8) : uAct u y ∈ K := by
  let S : Subalgebra ℂ (UniversalEnvelopingAlgebra ℂ L8) :=
    { carrier := {a | ∀ k ∈ K, uAct a k ∈ K}
      mul_mem' := fun {a b} ha hb k hk => by
        rw [uAct_mul]; exact ha _ (hb k hk)
      one_mem' := fun k hk => by rw [uAct_one]; exact hk
      add_mem' := fun {a b} ha hb k hk => by
        rw [uAct_add]; exact K.add_mem (ha k hk) (hb k hk)
      zero_mem' := fun k hk => by rw [map_zero]; exact K.zero_mem
      algebraMap_mem' := fun c k hk => by
        rw [Algebra.algebraMap_eq_smul_one, uAct_smul, uAct_one]
        exact K.smul_mem c hk }
  have hι : ∀ x : L8, UniversalEnvelopingAlgebra.ι ℂ x ∈ S := by
    intro x k hk
    rw [uAct_iota]
    exact K.lie_mem hk
  have htop : S = ⊤ := by
    have hle : (⊤ : Subalgebra ℂ (UniversalEnvelopingAlgebra ℂ L8)) ≤ S := by
      rw [← Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota]
      exact Algebra.adjoin_le (fun x hx => by obtain ⟨y, rfl⟩ := hx; exact hι y)
    exact le_antisymm le_top hle
  have hu : u ∈ S := by rw [htop]; trivial
  exact hu y hy

lemma N_le_of_mem (z : P) (K : LieSubmodule ℂ L8 P) (hz : z ∈ K) : N z ≤ K := by
  refine Submodule.span_le.mpr ?_
  rintro p ⟨u, rfl⟩
  exact uAct_mem_of_mem K hz u

lemma V_mem_N (z : P) (w : List (Fin 8)) : V z w ∈ N z := uAct_mem_Nsub z (fword w)

/-- The raising word applied to an annihilated vector gives `z` or `0`. -/
lemma eword_smul_z (z : P) (hzE : ∀ i, ⁅SerreE i, z⁆ = 0) (c : List (Fin 8)) :
    uAct (eword c) z = if c = [] then z else 0 := by
  induction c with
  | nil => simp
  | cons i t ih =>
      rw [eword, wordU_cons, uAct_mul, ih, if_neg (List.cons_ne_nil i t)]
      by_cases ht : t = []
      · subst ht
        rw [if_pos rfl, uAct_iota, hzE i]
      · rw [if_neg ht, map_zero]

/-- The Cartan word applied to a weight vector. -/
lemma hword_smul_z (z : P) (nu : Fin 8 → ℤ)
    (hzH : ∀ j, ⁅SerreH j, z⁆ = ((nu j : ℤ) : ℂ) • z) (v : List (Fin 8)) :
    uAct (hword v) z = (v.map (fun j => ((nu j : ℤ) : ℂ))).prod • z := by
  induction v with
  | nil => simp
  | cons j t ih =>
      rw [hword, wordU_cons, uAct_mul, ih, uAct_comm, uAct_iota, hzH, smul_smul, mul_comm]
      rw [List.map_cons, List.prod_cons]

/-- The triangular monomial acts on `z` inside the span of the word vectors. -/
lemma triMon_smul_z_mem (z : P) (nu : Fin 8 → ℤ)
    (hzE : ∀ i, ⁅SerreE i, z⁆ = 0) (hzH : ∀ j, ⁅SerreH j, z⁆ = ((nu j : ℤ) : ℂ) • z)
    (a b c : List (Fin 8)) :
    uAct (fword a * hword b * eword c) z ∈ Submodule.span ℂ (Set.range (V z)) := by
  rw [uAct_mul]
  rw [eword_smul_z z hzE c]
  by_cases hc : c = []
  · subst hc
    rw [if_pos rfl, uAct_mul, hword_smul_z z nu hzH b, uAct_comm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [if_neg hc, map_zero]
    exact Submodule.zero_mem _

/-- The submodule generated by a primitive vector is spanned by the word vectors. -/
lemma N_le_spanV (z : P) (nu : Fin 8 → ℤ)
    (hzE : ∀ i, ⁅SerreE i, z⁆ = 0) (hzH : ∀ j, ⁅SerreH j, z⁆ = ((nu j : ℤ) : ℂ) • z) :
    N z ≤ Submodule.span ℂ (Set.range (V z)) := by
  let φ : UniversalEnvelopingAlgebra ℂ L8 →ₗ[ℂ] P :=
    { toFun := fun u => uAct u z
      map_add' := fun u v => uAct_add u v z
      map_smul' := fun c u => uAct_smul c u z }
  have hgen : LieSubalgebra.lieSpan ℂ L8
      (Set.range SerreH ∪ Set.range SerreE ∪ Set.range SerreF) = ⊤ := by
    refine eq_top_of_lieSubalgebra_of_generators CartanMatrix.E₈ _ ?_
    intro g
    cases g with
    | H i =>
        change (SerreH i : L8) ∈ LieSubalgebra.lieSpan ℂ L8
          (Set.range SerreH ∪ Set.range SerreE ∪ Set.range SerreF)
        apply LieSubalgebra.subset_lieSpan
        exact Set.mem_union_left _ (Set.mem_union_left _ ⟨i, rfl⟩)
    | E i =>
        change (SerreE i : L8) ∈ LieSubalgebra.lieSpan ℂ L8
          (Set.range SerreH ∪ Set.range SerreE ∪ Set.range SerreF)
        apply LieSubalgebra.subset_lieSpan
        exact Set.mem_union_left _ (Set.mem_union_right _ ⟨i, rfl⟩)
    | F i =>
        change (SerreF i : L8) ∈ LieSubalgebra.lieSpan ℂ L8
          (Set.range SerreH ∪ Set.range SerreE ∪ Set.range SerreF)
        apply LieSubalgebra.subset_lieSpan
        exact Set.mem_union_right _ ⟨i, rfl⟩
  have htop := Commons.Algebra.Lie.TriangularSpan.span_triMon_eq_top (R := ℂ) (L := L8)
      (ι := Fin 8) (fun i j => ((E8 i j : ℤ) : ℂ)) SerreH SerreE SerreF hgen
      serreLie_HH serreLie_H_E_c serreLie_H_F_c serreLie_E_F
  have hmap : Submodule.map φ (Submodule.span ℂ
      (Set.range (fun p : List (Fin 8) × List (Fin 8) × List (Fin 8) =>
        (p.1.map (fun i => UniversalEnvelopingAlgebra.ι ℂ (SerreF i))).prod *
        (p.2.1.map (fun i => UniversalEnvelopingAlgebra.ι ℂ (SerreH i))).prod *
        (p.2.2.map (fun i => UniversalEnvelopingAlgebra.ι ℂ (SerreE i))).prod)))
      ≤ Submodule.span ℂ (Set.range (V z)) := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨⟨a, b, c⟩, rfl⟩
    exact triMon_smul_z_mem z nu hzE hzH a b c
  refine Submodule.span_le.mpr ?_
  rintro p ⟨u, rfl⟩
  exact hmap (Submodule.mem_map_of_mem (f := φ) (by rw [htop]; trivial))

lemma spanV_le_N (z : P) : Submodule.span ℂ (Set.range (V z)) ≤ N z := by
  refine Submodule.span_le.mpr ?_
  rintro p ⟨w, rfl⟩
  exact V_mem_N z w

/-- The span of the word vectors of length at most `m`. -/
noncomputable def P_m (z : P) (m : ℕ) : Submodule ℂ P :=
  Submodule.span ℂ (Set.range (fun w : {w : List (Fin 8) // w.length ≤ m} => V z w.1))

lemma P_m_mono (z : P) {m m' : ℕ} (h : m ≤ m') : P_m z m ≤ P_m z m' := by
  refine Submodule.span_le.mpr ?_
  rintro p ⟨w, rfl⟩
  exact Submodule.subset_span ⟨⟨w.1, le_trans w.2 h⟩, rfl⟩

lemma exists_P_m_of_mem_spanV (z : P) {p : P}
    (hp : p ∈ Submodule.span ℂ (Set.range (V z))) : ∃ m, p ∈ P_m z m := by
  refine Submodule.span_induction (p := fun x _ => ∃ m, x ∈ P_m z m) ?_ ?_ ?_ ?_ hp
  · rintro x ⟨w, rfl⟩
    exact ⟨w.length, Submodule.subset_span ⟨⟨w, le_rfl⟩, rfl⟩⟩
  · exact ⟨0, Submodule.zero_mem _⟩
  · rintro x y _ _ ⟨m, hm⟩ ⟨m', hm'⟩
    exact ⟨max m m', Submodule.add_mem _ (P_m_mono z (le_max_left _ _) hm)
      (P_m_mono z (le_max_right _ _) hm')⟩
  · rintro c x _ ⟨m, hm⟩
    exact ⟨m, Submodule.smul_mem _ c hm⟩

/-- The height operator `∑ wⱼ·ad(Hⱼ)`. -/
noncomputable def heightOp (ww : Fin 8 → ℂ) : Module.End ℂ P :=
  ∑ j, ww j • LieModule.toEnd ℂ L8 P (SerreH j)

/-- The sum identity `∑ j, w j * ∑_{i ∈ w} A j i = |w|`. -/
lemma sum_wsum_mul (ww : Fin 8 → ℂ) (hww : ∀ i, ∑ j, ww j * ((E8 j i : ℤ) : ℂ) = 1)
    (w : List (Fin 8)) :
    (∑ j, ww j * (w.map (fun i => ((E8 j i : ℤ) : ℂ))).sum) = (w.length : ℂ) := by
  induction w with
  | nil => simp
  | cons i t ih =>
      have hsplit : ∀ j, ww j * (List.map (fun i => ((E8 j i : ℤ) : ℂ)) (i :: t)).sum
          = ww j * ((E8 j i : ℤ) : ℂ)
            + ww j * (List.map (fun i => ((E8 j i : ℤ) : ℂ)) t).sum := by
        intro j; rw [List.map_cons, List.sum_cons, mul_add]
      rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib, ih, hww i]
      rw [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

/-- The height operator on a word vector. -/
lemma heightOp_V (z : P) (nu : Fin 8 → ℤ) (ww : Fin 8 → ℂ)
    (hww : ∀ i, ∑ j, ww j * ((E8 j i : ℤ) : ℂ) = 1)
    (hzH : ∀ j, ⁅SerreH j, z⁆ = ((nu j : ℤ) : ℂ) • z) (w : List (Fin 8)) :
    heightOp ww (V z w)
      = ((∑ j, ww j * ((nu j : ℤ) : ℂ)) - (w.length : ℂ)) • V z w := by
  rw [heightOp, LinearMap.sum_apply]
  have hterm : ∀ j : Fin 8, (ww j • LieModule.toEnd ℂ L8 P (SerreH j)) (V z w)
      = (ww j * (((nu j : ℤ) : ℂ) - (w.map (fun i => ((E8 j i : ℤ) : ℂ))).sum)) • V z w := by
    intro j
    rw [LinearMap.smul_apply, LieModule.toEnd_apply_apply, iotaH_V z nu hzH j w, smul_smul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_smul]
  congr 1
  rw [Finset.sum_congr rfl (fun j _ => mul_sub (ww j) _ _), Finset.sum_sub_distrib,
    sum_wsum_mul ww hww w]

/-- The iterated operator `∏_{k=1}^m (A - (h₀ - k))`. -/
noncomputable def iterOp (A : Module.End ℂ P) (h₀ : ℂ) : ℕ → Module.End ℂ P
  | 0 => 1
  | (m + 1) => iterOp A h₀ m * (A - (h₀ - (((m + 1 : ℕ)) : ℂ)) • (1 : Module.End ℂ P))

lemma iterOp_succ (A : Module.End ℂ P) (h₀ : ℂ) (m : ℕ) :
    iterOp A h₀ (m + 1)
      = iterOp A h₀ m * (A - (h₀ - (((m + 1 : ℕ)) : ℂ)) • (1 : Module.End ℂ P)) := rfl

/-- Evaluation of the iterated operator on an eigenvector. -/
lemma iterOp_apply_of_eigen {A : Module.End ℂ P} {v : P} {c : ℂ} (hA : A v = c • v)
    (h₀ : ℂ) : ∀ m : ℕ, iterOp A h₀ m v
      = (∏ k ∈ Finset.range m, (c - h₀ + (((k + 1 : ℕ)) : ℂ))) • v
  | 0 => by simp [iterOp]
  | (m + 1) => by
      rw [iterOp_succ, Module.End.mul_apply]
      have hB : (A - (h₀ - (((m + 1 : ℕ)) : ℂ)) • (1 : Module.End ℂ P)) v
          = (c - h₀ + (((m + 1 : ℕ)) : ℂ)) • v := by
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hA]
        module
      rw [hB, map_smul, iterOp_apply_of_eigen hA h₀ m, smul_smul, Finset.prod_range_succ,
        mul_comm]

/-- The operator `∏_{k=1}^m (𝔥 - (h₀ - k))` built from the height operator. -/
noncomputable def Qop (ww : Fin 8 → ℂ) (h₀ : ℂ) (m : ℕ) : Module.End ℂ P :=
  iterOp (heightOp ww) h₀ m

lemma Qop_apply_V (z : P) (nu : Fin 8 → ℤ) (ww : Fin 8 → ℂ)
    (hww : ∀ i, ∑ j, ww j * ((E8 j i : ℤ) : ℂ) = 1)
    (hzH : ∀ j, ⁅SerreH j, z⁆ = ((nu j : ℤ) : ℂ) • z) (m : ℕ) (w : List (Fin 8)) :
    Qop ww (∑ j, ww j * ((nu j : ℤ) : ℂ)) m (V z w)
      = (∏ k ∈ Finset.range m, ((((k + 1 : ℕ)) : ℂ) - (w.length : ℂ))) • V z w := by
  rw [Qop, iterOp_apply_of_eigen (heightOp_V z nu ww hww hzH w) _ m]
  congr 1
  have hk : ∀ k : ℕ, (∑ j, ww j * ((nu j : ℤ) : ℂ)) - (w.length : ℂ)
        - (∑ j, ww j * ((nu j : ℤ) : ℂ)) + (((k + 1 : ℕ)) : ℂ)
      = (((k + 1 : ℕ)) : ℂ) - (w.length : ℂ) := fun k => by ring
  simp only [hk]

lemma Qop_apply_V_mem (z : P) (nu : Fin 8 → ℤ) (ww : Fin 8 → ℂ)
    (hww : ∀ i, ∑ j, ww j * ((E8 j i : ℤ) : ℂ) = 1)
    (hzH : ∀ j, ⁅SerreH j, z⁆ = ((nu j : ℤ) : ℂ) • z) :
    ∀ (m : ℕ) {w : List (Fin 8)}, w.length ≤ m →
      Qop ww (∑ j, ww j * ((nu j : ℤ) : ℂ)) m (V z w) ∈ Submodule.span ℂ ({z} : Set P)
  | 0, w, hw => by
      have h0 : w.length = 0 := Nat.le_zero.mp hw
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero h0
      rw [hw0, V_nil, Qop]
      exact Submodule.subset_span (Set.mem_singleton z)
  | (m + 1), w, hw => by
      rw [Qop, iterOp_succ]
      set B : Module.End ℂ P := (heightOp ww)
        - ((∑ j, ww j * ((nu j : ℤ) : ℂ)) - (((m + 1 : ℕ)) : ℂ)) • (1 : Module.End ℂ P)
        with hBdef
      have hB : B (V z w) = ((((m + 1 : ℕ)) : ℂ) - (w.length : ℂ)) • V z w := by
        rw [hBdef, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          heightOp_V z nu ww hww hzH w]
        module
      rw [Module.End.mul_apply, hB]
      by_cases hcase : w.length = m + 1
      · rw [hcase, sub_self, zero_smul, map_zero]
        exact Submodule.zero_mem _
      · have hw' : w.length ≤ m := by omega
        rw [map_smul]
        exact Submodule.smul_mem _ _ (Qop_apply_V_mem z nu ww hww hzH m hw')

lemma Qop_mem_span_singleton (z : P) (nu : Fin 8 → ℤ) (ww : Fin 8 → ℂ)
    (hww : ∀ i, ∑ j, ww j * ((E8 j i : ℤ) : ℂ) = 1)
    (hzH : ∀ j, ⁅SerreH j, z⁆ = ((nu j : ℤ) : ℂ) • z) (m : ℕ) {p : P}
    (hp : p ∈ P_m z m) :
    Qop ww (∑ j, ww j * ((nu j : ℤ) : ℂ)) m p ∈ Submodule.span ℂ ({z} : Set P) := by
  refine Submodule.span_induction (p := fun x _ =>
    Qop ww (∑ j, ww j * ((nu j : ℤ) : ℂ)) m x ∈ Submodule.span ℂ ({z} : Set P))
    ?_ ?_ ?_ ?_ hp
  · rintro x ⟨w, rfl⟩
    exact Qop_apply_V_mem z nu ww hww hzH m w.2
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx

lemma heightOp_mem_of_mem (ww : Fin 8 → ℂ) (K : LieSubmodule ℂ L8 P) {y : P} (hy : y ∈ K) :
    heightOp ww y ∈ K := by
  rw [heightOp, LinearMap.sum_apply]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [LinearMap.smul_apply, LieModule.toEnd_apply_apply]
  exact K.smul_mem _ (K.lie_mem hy)

lemma iterOp_mem_of_mem (K : LieSubmodule ℂ L8 P) (A : Module.End ℂ P) (h₀ : ℂ)
    (hA : ∀ y ∈ K, A y ∈ K) (m : ℕ) {y : P} (hy : y ∈ K) : iterOp A h₀ m y ∈ K := by
  induction m generalizing y with
  | zero => simpa [iterOp] using hy
  | succ m ih =>
      rw [iterOp_succ, Module.End.mul_apply]
      refine ih ?_
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact K.sub_mem (hA y hy) (K.smul_mem _ hy)

lemma Qop_mem_of_mem (ww : Fin 8 → ℂ) (h₀ : ℂ) (K : LieSubmodule ℂ L8 P) {y : P}
    (hy : y ∈ K) (m : ℕ) : Qop ww h₀ m y ∈ K :=
  iterOp_mem_of_mem K (heightOp ww) h₀ (fun y hy => heightOp_mem_of_mem ww K hy) m hy

/-- **The sum of two proper submodules of `N` is proper.** -/
theorem sup_ne_N_of_ne_N (z : P) (nu : Fin 8 → ℤ) (hz : z ≠ 0)
    (hzE : ∀ i, ⁅SerreE i, z⁆ = 0) (hzH : ∀ j, ⁅SerreH j, z⁆ = ((nu j : ℤ) : ℂ) • z)
    (K K' : LieSubmodule ℂ L8 P) (hK : K ≤ N z) (hK' : K' ≤ N z)
    (hKne : K ≠ N z) (hK'ne : K' ≠ N z) : K ⊔ K' ≠ N z := by
  intro hsup
  obtain ⟨ww, hww⟩ := Commons.LinearAlgebra.Matrix.Cartan.exists_w_mul_E8
  have hzK : z ∉ K := fun hz' => hKne (le_antisymm hK (N_le_of_mem z K hz'))
  have hzK' : z ∉ K' := fun hz' => hK'ne (le_antisymm hK' (N_le_of_mem z K' hz'))
  have hzmem : z ∈ K ⊔ K' := by rw [hsup]; exact self_mem_N z
  obtain ⟨k, hkK, k', hk'K', hkadd⟩ := (LieSubmodule.mem_sup K K' z).mp hzmem
  have hkN : k ∈ N z := hK hkK
  have hk'N : k' ∈ N z := hK' hk'K'
  obtain ⟨m, hm⟩ := exists_P_m_of_mem_spanV z (N_le_spanV z nu hzE hzH hkN)
  obtain ⟨m', hm'⟩ := exists_P_m_of_mem_spanV z (N_le_spanV z nu hzE hzH hk'N)
  have hdisj : ∀ (L : LieSubmodule ℂ L8 P), L ≤ N z → z ∉ L →
      ∀ y ∈ Submodule.span ℂ ({z} : Set P), y ∈ L → y = 0 := by
    intro L hL hzL y hy hyL
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨c, rfl⟩ := hy
    by_cases hc : c = 0
    · rw [hc, zero_smul]
    · exact absurd (by
        have h1 : z = c⁻¹ • (c • z) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        rw [h1]; exact L.smul_mem _ hyL) hzL
  have hQk : Qop ww (∑ j, ww j * ((nu j : ℤ) : ℂ)) (max m m') k = 0 := by
    refine hdisj K hK hzK _ (Qop_mem_span_singleton z nu ww hww hzH _ (P_m_mono z (le_max_left _ _) hm)) ?_
    exact Qop_mem_of_mem ww _ K hkK _
  have hQk' : Qop ww (∑ j, ww j * ((nu j : ℤ) : ℂ)) (max m m') k' = 0 := by
    refine hdisj K' hK' hzK' _ (Qop_mem_span_singleton z nu ww hww hzH _ (P_m_mono z (le_max_right _ _) hm')) ?_
    exact Qop_mem_of_mem ww _ K' hk'K' _
  have hQz : Qop ww (∑ j, ww j * ((nu j : ℤ) : ℂ)) (max m m') z
      = (∏ k ∈ Finset.range (max m m'), (((k + 1 : ℕ)) : ℂ)) • z := by
    have h := Qop_apply_V z nu ww hww hzH (max m m') ([] : List (Fin 8))
    simpa using h
  have hzero : Qop ww (∑ j, ww j * ((nu j : ℤ) : ℂ)) (max m m') z = 0 := by
    rw [← hkadd, map_add, hQk, hQk', zero_add]
  rw [hQz] at hzero
  have hprod : (∏ k ∈ Finset.range (max m m'), (((k + 1 : ℕ)) : ℂ)) ≠ 0 := by
    rw [← Nat.cast_prod]
    exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun k _ => Nat.succ_ne_zero k)
  exact hz ((smul_eq_zero.mp hzero).resolve_left hprod)

end General

theorem lieEquiv_of_same_primitive_weight {M M' : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule Commons.Algebra.Lie.SerreConstruction.L8 M]
    [LieModule ℂ Commons.Algebra.Lie.SerreConstruction.L8 M] [Module.Finite ℂ M]
    [AddCommGroup M'] [Module ℂ M'] [LieRingModule Commons.Algebra.Lie.SerreConstruction.L8 M']
    [LieModule ℂ Commons.Algebra.Lie.SerreConstruction.L8 M'] [Module.Finite ℂ M']
    (hM : LieModule.IsIrreducible ℂ Commons.Algebra.Lie.SerreConstruction.L8 M)
    (hM' : LieModule.IsIrreducible ℂ Commons.Algebra.Lie.SerreConstruction.L8 M')
    {ν : Fin 8 → ℤ} {x : M} {x' : M'}
    (hx : x ≠ 0)
    (hxE : ∀ i, ⁅Commons.Algebra.Lie.SerreConstruction.SerreE i, x⁆ = 0)
    (hxH : ∀ i, ⁅Commons.Algebra.Lie.SerreConstruction.SerreH i, x⁆ = ((ν i : ℤ) : ℂ) • x)
    (hx' : x' ≠ 0)
    (hx'E : ∀ i, ⁅Commons.Algebra.Lie.SerreConstruction.SerreE i, x'⁆ = 0)
    (hx'H : ∀ i, ⁅Commons.Algebra.Lie.SerreConstruction.SerreH i, x'⁆ = ((ν i : ℤ) : ℂ) • x') :
    Nonempty (M ≃ₗ⁅ℂ, Commons.Algebra.Lie.SerreConstruction.L8⁆ M') := by
  classical
  set z : M × M' := (x, x') with hzdef
  have hzfst : z.1 = x := by simp [hzdef]
  have hzsnd : z.2 = x' := by simp [hzdef]
  have hz : z ≠ 0 := by
    intro h
    exact hx (by rw [hzdef] at h; exact (Prod.ext_iff.mp h).1)
  have hzE : ∀ i, ⁅SerreE i, z⁆ = 0 := by
    intro i
    rw [hzdef]
    show (⁅SerreE i, x⁆, ⁅SerreE i, x'⁆) = ((0 : M), (0 : M'))
    rw [hxE i, hx'E i]
  have hzH : ∀ j, ⁅SerreH j, z⁆ = ((ν j : ℤ) : ℂ) • z := by
    intro j
    rw [hzdef]
    show (⁅SerreH j, x⁆, ⁅SerreH j, x'⁆) = ((ν j : ℤ) : ℂ) • (x, x')
    rw [hxH j, hx'H j, Prod.smul_mk]
  -- the two projections
  let pr1 : (M × M') →ₗ⁅ℂ,L8⁆ M :=
    { toLinearMap := { toFun := Prod.fst, map_add' := fun a b => rfl, map_smul' := fun c a => rfl }
      map_lie' := fun {a b} => rfl }
  let pr2 : (M × M') →ₗ⁅ℂ,L8⁆ M' :=
    { toLinearMap := { toFun := Prod.snd, map_add' := fun a b => rfl, map_smul' := fun c a => rfl }
      map_lie' := fun {a b} => rfl }
  have hpr1 : ∀ p : M × M', pr1 p = p.1 := fun p => rfl
  have hpr2 : ∀ p : M × M', pr2 p = p.2 := fun p => rfl
  let K1 : LieSubmodule ℂ L8 (M × M') := pr1.ker ⊓ N z
  let K2 : LieSubmodule ℂ L8 (M × M') := pr2.ker ⊓ N z
  have hK1le : K1 ≤ N z := inf_le_right
  have hK2le : K2 ≤ N z := inf_le_right
  have hK1mem : ∀ p : M × M', p ∈ K1 ↔ (p.1 = 0 ∧ p ∈ N z) := by
    intro p
    refine ⟨fun h => ⟨?_, h.2⟩, fun h => ⟨?_, h.2⟩⟩
    · have := (LieModuleHom.mem_ker).mp h.1
      rwa [hpr1] at this
    · exact (LieModuleHom.mem_ker).mpr (by rw [hpr1]; exact h.1)
  have hK2mem : ∀ p : M × M', p ∈ K2 ↔ (p.2 = 0 ∧ p ∈ N z) := by
    intro p
    refine ⟨fun h => ⟨?_, h.2⟩, fun h => ⟨?_, h.2⟩⟩
    · have := (LieModuleHom.mem_ker).mp h.1
      rwa [hpr2] at this
    · exact (LieModuleHom.mem_ker).mpr (by rw [hpr2]; exact h.1)
  have hzK1 : z ∉ K1 := by
    intro h
    exact hx (by rw [← hzfst]; exact (hK1mem z).mp h |>.1)
  have hzK2 : z ∉ K2 := by
    intro h
    exact hx' (by rw [← hzsnd]; exact (hK2mem z).mp h |>.1)
  have hK1ne : K1 ≠ N z := fun h => hzK1 (h ▸ self_mem_N z)
  have hK2ne : K2 ≠ N z := fun h => hzK2 (h ▸ self_mem_N z)
  -- maximality of the kernels
  have hK1max : ∀ L : LieSubmodule ℂ L8 (M × M'), K1 < L → L ≤ N z → L = N z := by
    intro L hlt hL
    by_contra hLne
    have hex : ∃ y ∈ L, y ∉ K1 := by
      by_contra h
      push Not at h
      exact (lt_iff_le_not_ge.mp hlt).2 (fun y hy => h y hy)
    obtain ⟨y, hyL, hyK1⟩ := hex
    have hy1 : y.1 ≠ 0 := by
      intro h0
      exact hyK1 ((hK1mem y).mpr ⟨h0, hL hyL⟩)
    have hmap : LieSubmodule.map pr1 L = ⊤ := by
      rcases eq_bot_or_eq_top (LieSubmodule.map pr1 L) with h | h
      · exfalso
        have hy : pr1 y ∈ LieSubmodule.map pr1 L :=
          (LieSubmodule.mem_map (f := pr1) (N := L) (pr1 y)).mpr ⟨y, hyL, rfl⟩
        rw [h] at hy
        exact hy1 (by simpa [hpr1] using hy)
      · exact h
    have hxmem : x ∈ LieSubmodule.map pr1 L := by rw [hmap]; trivial
    obtain ⟨l, hlL, hl⟩ := (LieSubmodule.mem_map (f := pr1) (N := L) x).mp hxmem
    have hdiff : l - z ∈ K1 := by
      refine (hK1mem _).mpr ⟨?_, (N z).sub_mem (hL hlL) (self_mem_N z)⟩
      change l.1 - z.1 = 0
      rw [← hpr1 l, hl, hzfst, sub_self]
    have hzL : z ∈ L := by
      have : l - (l - z) = z := by abel
      rw [← this]
      exact L.sub_mem hlL (hlt.le hdiff)
    exact hLne (le_antisymm hL (N_le_of_mem z L hzL))
  have hK2max : ∀ L : LieSubmodule ℂ L8 (M × M'), K2 < L → L ≤ N z → L = N z := by
    intro L hlt hL
    by_contra hLne
    have hex : ∃ y ∈ L, y ∉ K2 := by
      by_contra h
      push Not at h
      exact (lt_iff_le_not_ge.mp hlt).2 (fun y hy => h y hy)
    obtain ⟨y, hyL, hyK2⟩ := hex
    have hy2 : y.2 ≠ 0 := by
      intro h0
      exact hyK2 ((hK2mem y).mpr ⟨h0, hL hyL⟩)
    have hmap : LieSubmodule.map pr2 L = ⊤ := by
      rcases eq_bot_or_eq_top (LieSubmodule.map pr2 L) with h | h
      · exfalso
        have hy : pr2 y ∈ LieSubmodule.map pr2 L :=
          (LieSubmodule.mem_map (f := pr2) (N := L) (pr2 y)).mpr ⟨y, hyL, rfl⟩
        rw [h] at hy
        exact hy2 (by simpa [hpr2] using hy)
      · exact h
    have hxmem : x' ∈ LieSubmodule.map pr2 L := by rw [hmap]; trivial
    obtain ⟨l, hlL, hl⟩ := (LieSubmodule.mem_map (f := pr2) (N := L) x').mp hxmem
    have hdiff : l - z ∈ K2 := by
      refine (hK2mem _).mpr ⟨?_, (N z).sub_mem (hL hlL) (self_mem_N z)⟩
      change l.2 - z.2 = 0
      rw [← hpr2 l, hl, hzsnd, sub_self]
    have hzL : z ∈ L := by
      have : l - (l - z) = z := by abel
      rw [← this]
      exact L.sub_mem hlL (hlt.le hdiff)
    exact hLne (le_antisymm hL (N_le_of_mem z L hzL))
  -- the two kernels coincide
  have hK12 : K1 = K2 := by
    by_contra hne
    have hsup : K1 ⊔ K2 = N z := by
      by_contra hsupne
      have h1 : K1 ⊔ K2 = K1 := by
        by_contra h2
        exact hsupne (hK1max (K1 ⊔ K2) (lt_of_le_of_ne le_sup_left (Ne.symm h2))
          (sup_le hK1le hK2le))
      have hK2K1 : K2 ≤ K1 := by rw [← h1]; exact le_sup_right
      exact hK1ne (hK2max K1 (lt_of_le_of_ne hK2K1 (Ne.symm hne)) hK1le)
    exact (sup_ne_N_of_ne_N z ν hz hzE hzH K1 K2 hK1le hK2le hK1ne hK2ne) hsup
  have hK1bot : K1 = ⊥ := by
    rw [LieSubmodule.eq_bot_iff]
    intro y hy
    have h1 : y.1 = 0 := (hK1mem y).mp hy |>.1
    have h2 : y.2 = 0 := (hK2mem y).mp (hK12 ▸ hy) |>.1
    exact Prod.ext h1 h2
  haveI : Nonempty ↥(N z) := ⟨⟨z, self_mem_N z⟩⟩
  -- the two projections restricted to `N`
  let g1 : ↥(N z) →ₗ⁅ℂ,L8⁆ M :=
    { toFun := fun y => y.1.1
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl
      map_lie' := fun {a b} => rfl }
  let g2 : ↥(N z) →ₗ⁅ℂ,L8⁆ M' :=
    { toFun := fun y => y.1.2
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl
      map_lie' := fun {a b} => rfl }
  have hg1ker : g1.ker = ⊥ := by
    rw [LieSubmodule.eq_bot_iff]
    intro y hy
    have hy1 : y.1 ∈ K1 := (hK1mem y.1).mpr ⟨?_, y.2⟩
    · rw [hK1bot] at hy1
      exact Subtype.ext (by simpa using hy1)
    · exact (LieModuleHom.mem_ker).mp hy
  have hg2ker : g2.ker = ⊥ := by
    rw [LieSubmodule.eq_bot_iff]
    intro y hy
    have hy2 : y.1 ∈ K2 := (hK2mem y.1).mpr ⟨?_, y.2⟩
    · rw [show K2 = ⊥ from hK12 ▸ hK1bot] at hy2
      exact Subtype.ext (by simpa using hy2)
    · exact (LieModuleHom.mem_ker).mp hy
  have hg1range : g1.range = ⊤ := by
    rcases eq_bot_or_eq_top g1.range with h | h
    · exfalso
      have hxmem : x ∈ g1.range := (LieModuleHom.mem_range g1 x).mpr
        ⟨⟨z, self_mem_N z⟩, by show pr1 z = x; rw [hzdef]; rfl⟩
      rw [h] at hxmem
      exact hx (by simpa using hxmem)
    · exact h
  have hg2range : g2.range = ⊤ := by
    rcases eq_bot_or_eq_top g2.range with h | h
    · exfalso
      have hxmem : x' ∈ g2.range := (LieModuleHom.mem_range g2 x').mpr
        ⟨⟨z, self_mem_N z⟩, by show pr2 z = x'; rw [hzdef]; rfl⟩
      rw [h] at hxmem
      exact hx' (by simpa using hxmem)
    · exact h
  have hinj1 := (LieModuleHom.ker_eq_bot g1).mp hg1ker
  have hsurj1 := (LieModuleHom.range_eq_top g1).mp hg1range
  have hinj2 := (LieModuleHom.ker_eq_bot g2).mp hg2ker
  have hsurj2 := (LieModuleHom.range_eq_top g2).mp hg2range
  refine ⟨(LieModuleEquiv.mk g1 (Function.invFun g1)
      (Function.leftInverse_invFun hinj1) (Function.rightInverse_invFun hsurj1)).symm.trans
    (LieModuleEquiv.mk g2 (Function.invFun g2)
      (Function.leftInverse_invFun hinj2) (Function.rightInverse_invFun hsurj2))⟩


end Commons.Algebra.Lie.SerreConstruction

end
