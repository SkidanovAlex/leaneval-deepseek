import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDEstimates.eNorm_sub_le
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.numaux.rk_span_eq
import Submission.Work.HP.numaux.rk_satLat
import Submission.Work.HP.numaux.satLat_span
import Submission.Work.HP.numaux.doubleOrth_eq_satLat
import Submission.Work.HP.numaux.lam_le_iff
import Submission.Work.HP.Q44Child.SuperDefs
import Submission.Work.HP.Q44Child.snoc_linIndep
import Submission.Work.HP.Q44Child.exists_chain3


/-!
# `Work.HP.Q44Child.ballCount_le`

Lattice point count for a rank-`3` sublattice `L ⊆ ℤ^5`:

`#(L ∩ B_T) ≤ 27 * ∏_{i=1}^{3} (1 + T / λ_i(L))`,  `λ_i = lam L i`.

## Status: complete

The bound is proved via Henk's coset lemma (`henkCoset`) applied to a *flag-adapted*
`ℤ`-basis `b₀,b₁,b₂` of `L` and the diagonal sublattice `Λ̃ = ℤ(m₁b₀) ⊕ ℤ(m₂b₁) ⊕ ℤ(m₃b₂)`:

* `henkCoset` — Henk, *Successive minima and lattice points* (arXiv:math/0204158), Lemma 2.1, in
  the "labelled cosets" form needed (proved here);
* `exists_flagBasis` — a `ℤ`-basis of `L` with `{v ∈ L : ‖v‖ < λ₂} ⊆ ℝb₀` and
  `{v ∈ L : ‖v‖ < λ₃} ⊆ ℝb₀ + ℝb₁` (proved here, via Smith normal form);
* `kill_At` — the level argument showing `Λ̃ ∩ {eNorm ≤ 2T} = {0}` (proved here);
* `ballCount_le_of_basis` — the assembly (proved here).

Imported inputs: `Work.HP.Q44Child.exists_chain3` (the chain `m₃ ∣ m₂ ∣ m₁` with
`m₁m₂m₃ ≤ 27 ∏(1+T/λᵢ)`), `Work.HP.lam_basic`, `Work.HP.MDEstimates.eNorm_sub_le`,
`Work.HP.MDBasic.finite_eNorm_le`, the `Work.HP.numaux.*` saturation/Smith toolkit, and
`Work.HP.Q44Child.SuperDefs` (`toE` etc.).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Finset

namespace Work.HP.Q44Child

variable {ι : Type*}

/-- Henk's coset lemma, "labelled cosets" form: if `label` is constant on cosets of `A`
inside `L` then `#(S ∩ L) ≤ #(labels) * #((S - S) ∩ A)`.

Proof: let `T = {x : L | ↑x ∈ S}` and, for each label class, choose a base point `base k` in it.
The map `x ↦ (label x, ↑x - ↑(base (label x)))` is injective on `T` (subtract and cancel) and
lands in `κ × D` with `D = A ∩ (S - S)`; comparing cardinals gives the result. -/
theorem henkCoset (L A : Submodule ℤ (ι → ℤ)) (hA : A ≤ L) (S : Set (ι → ℤ)) (hS : S.Finite)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (label : L → κ)
    (hlabel : ∀ x y : L, label x = label y → ((x : ι → ℤ) - (y : ι → ℤ)) ∈ A) :
    ({x : ι → ℤ | x ∈ L ∧ x ∈ S} : Set (ι → ℤ)).ncard
      ≤ Fintype.card κ * ({x : ι → ℤ | x ∈ A ∧ ∃ y ∈ S, ∃ z ∈ S, y - z = x} : Set (ι → ℤ)).ncard := by
  classical
  set T : Set L := {x | (x : ι → ℤ) ∈ S} with hT
  have hTfin : T.Finite := hS.preimage (fun a _ b _ h => Subtype.ext h)
  set D : Set (ι → ℤ) := {x | x ∈ A ∧ ∃ y ∈ S, ∃ z ∈ S, y - z = x} with hD
  have hDfin : D.Finite := by
    have h1 : ({x : ι → ℤ | ∃ y ∈ S, ∃ z ∈ S, y - z = x}).Finite :=
      Set.Finite.image2 (fun y z : ι → ℤ => y - z) hS hS
    exact h1.subset (fun x hx => hx.2)
  let base : κ → L := fun k => if h : (T ∩ {x | label x = k}).Nonempty then h.choose else 0
  have hbase : ∀ k : κ, (T ∩ {x | label x = k}).Nonempty → base k ∈ T ∧ label (base k) = k := by
    intro k h
    have hspec := h.choose_spec
    simp only [base, dif_pos h]
    exact hspec
  let φ : L → κ × (ι → ℤ) := fun x => (label x, (x : ι → ℤ) - ((base (label x) : L) : ι → ℤ))
  have hφ_mem : ∀ x ∈ T, φ x ∈ Set.univ ×ˢ D := by
    intro x hx
    have hne : (T ∩ {y : L | label y = label x}).Nonempty := ⟨x, hx, rfl⟩
    obtain ⟨hbT, hbl⟩ := hbase (label x) hne
    exact ⟨trivial, hlabel x (base (label x)) hbl.symm,
      ⟨x, hx, base (label x), hbT, rfl⟩⟩
  have hφ_inj : Set.InjOn φ T := by
    intro x hx y hy hxy
    have h1 : label x = label y := congrArg Prod.fst hxy
    have h2 : (x : ι → ℤ) - ((base (label x) : L) : ι → ℤ)
        = (y : ι → ℤ) - ((base (label y) : L) : ι → ℤ) := congrArg Prod.snd hxy
    rw [h1] at h2
    have : (x : ι → ℤ) = (y : ι → ℤ) := by
      have h3 := congrArg (fun w : ι → ℤ => w + ((base (label y) : L) : ι → ℤ)) h2
      simpa using h3
    exact Subtype.ext this
  have hcardT : ({x : ι → ℤ | x ∈ L ∧ x ∈ S} : Set (ι → ℤ)).ncard = T.ncard := by
    have hset : ({x : ι → ℤ | x ∈ L ∧ x ∈ S} : Set (ι → ℤ)) = Subtype.val '' T := by
      ext x
      constructor
      · rintro ⟨hxL, hxS⟩
        exact ⟨⟨x, hxL⟩, hxS, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
    rw [hset]
    exact Set.ncard_image_of_injective T Subtype.val_injective
  rw [hcardT]
  calc T.ncard ≤ (Set.univ ×ˢ D).ncard :=
        Set.ncard_le_ncard_of_injOn φ hφ_mem hφ_inj (Set.finite_univ.prod hDfin)
    _ = Fintype.card κ * D.ncard := by rw [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card]
    _ = Fintype.card κ * ({x : ι → ℤ | x ∈ A ∧ ∃ y ∈ S, ∃ z ∈ S, y - z = x} : Set (ι → ℤ)).ncard := by
        rw [hD]

/-- `lam L k ≤ N` as soon as `L` contains `k` `ℤ`-linearly independent vectors of norm `≤ N`. -/
lemma lam_le_of_norm_le {L : Submodule ℤ (Fin 5 → ℤ)} {k : ℕ} {f : Fin k → (Fin 5 → ℤ)}
    (hfL : ∀ j, f j ∈ L) (hli : LinearIndependent ℤ f) {N : ℝ} (hN0 : 0 ≤ N)
    (hN : ∀ j, Work.HP.eNorm (f j) ≤ N) : Work.HP.lam L k ≤ N :=
  csInf_le (bddBelow_lamSet L k) ⟨hN0, f, hfL, hli, hN⟩

/-- Scalar cancellation in a real vector space. -/
lemma smul_eq_of_inv_smul {z w : E5} {c : ℝ} (hc : c ≠ 0) (h : c • z = w) : z = c⁻¹ • w := by
  have h7 := congrArg (fun u : E5 => c⁻¹ • u) h
  rwa [inv_smul_smul₀ hc z] at h7

/-- Two integer vectors whose images under `toE` are not parallel are `ℤ`-independent. -/
lemma linearIndependent_int_pair {a x : Fin 5 → ℤ} (hta : toE a ≠ 0)
    (hcon : ∀ t : ℝ, toE x ≠ t • toE a) : LinearIndependent ℤ ![a, x] := by
  have hR : LinearIndependent ℝ (![toE a, toE x] : Fin 2 → E5) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum : c 0 • toE a + c 1 • toE x = 0 := by
      have h := hc
      rw [Fin.sum_univ_two] at h
      simpa using h
    have hz1 : c 1 = 0 := by
      by_contra h1
      have h4 : c 1 • toE x = (-(c 0)) • toE a := by
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_right hsum
      have h5 := smul_eq_of_inv_smul h1 h4
      refine hcon ((c 1)⁻¹ * (-(c 0))) ?_
      simpa only [smul_smul] using h5
    have hz0 : c 0 = 0 := by
      rw [hz1, zero_smul, add_zero] at hsum
      rcases smul_eq_zero.mp hsum with h5 | h5
      · exact h5
      · exact absurd h5 hta
    intro i
    fin_cases i <;> assumption
  rw [Fintype.linearIndependent_iff] at hR ⊢
  intro c hc i
  have hsum : c 0 • a + c 1 • x = 0 := by
    have h := hc
    rw [Fin.sum_univ_two] at h
    simpa using h
  have hRsum : (∑ j : Fin 2, ((c j : ℤ) : ℝ) • (![toE a, toE x] : Fin 2 → E5) j) = 0 := by
    rw [Fin.sum_univ_two]
    have h := congrArg (fun v : Fin 5 → ℤ => toE v) hsum
    rw [map_add, map_smul, map_smul, map_zero] at h
    rw [← Int.cast_smul_eq_zsmul ℝ (c 0) (toE a),
      ← Int.cast_smul_eq_zsmul ℝ (c 1) (toE x)] at h
    simpa using h
  have := hR (fun j => ((c j : ℤ) : ℝ)) hRsum i
  exact_mod_cast this

/-- `lam L 2` flag: `x ∈ L` of norm `< lam L 2` is parallel to the shortest vector `a`. -/
lemma exists_smul_toE_of_eNorm_lt_lam2 {L : Submodule ℤ (Fin 5 → ℤ)} {a x : Fin 5 → ℤ}
    (haL : a ∈ L) (ha : Work.HP.eNorm a ≤ Work.HP.lam L 1) (ha0 : a ≠ 0)
    (hxL : x ∈ L) (hx : Work.HP.eNorm x < Work.HP.lam L 2) :
    ∃ t : ℝ, toE x = t • toE a := by
  by_contra hcon
  push Not at hcon
  have hta : toE a ≠ 0 := fun h => ha0 (toE_injective (by simpa using h))
  have hli := linearIndependent_int_pair hta hcon
  have hx0 : x ≠ 0 := by rintro rfl; exact hcon 0 (by simp)
  have hax : Work.HP.eNorm a ≤ Work.HP.eNorm x :=
    le_trans ha (Work.HP.lam_one_le_eNorm L hxL hx0)
  have hmax : Work.HP.lam L 2 ≤ max (Work.HP.eNorm a) (Work.HP.eNorm x) :=
    lam_le_of_norm_le (L := L) (k := 2) (f := ![a, x])
      (by intro j; fin_cases j <;> simp [haL, hxL])
      hli
      (le_trans (Work.HP.eNorm_nonneg a) (le_max_left _ _))
      (by intro j; fin_cases j <;> simp [hax])
  rw [max_eq_right hax] at hmax
  linarith

/-- A triple containing a vector outside the real span of an independent pair is `ℤ`-independent. -/
lemma linearIndependent_int_triple {a₁ a₂ x : Fin 5 → ℤ} (hli : LinearIndependent ℤ ![a₁, a₂])
    (hx : toE x ∉ Submodule.span ℝ (Set.range fun i : Fin 2 => toE (![a₁, a₂] i))) :
    LinearIndependent ℤ ![a₁, a₂, x] := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  have hsum : c 0 • a₁ + c 1 • a₂ + c 2 • x = 0 := by
    have h := hc
    rw [Fin.sum_univ_three] at h
    simpa using h
  have hc2 : c 2 = 0 := by
    by_contra h2
    have h2R : (c 2 : ℝ) ≠ 0 := by exact_mod_cast h2
    have hR : (c 0 : ℝ) • toE a₁ + (c 1 : ℝ) • toE a₂ + (c 2 : ℝ) • toE x = 0 := by
      have h := congrArg (fun v : Fin 5 → ℤ => toE v) hsum
      rw [map_add, map_add, map_smul, map_smul, map_smul, map_zero] at h
      rw [← Int.cast_smul_eq_zsmul ℝ (c 0) (toE a₁),
        ← Int.cast_smul_eq_zsmul ℝ (c 1) (toE a₂),
        ← Int.cast_smul_eq_zsmul ℝ (c 2) (toE x)] at h
      exact h
    have h4 : (c 2 : ℝ) • toE x = -((c 0 : ℝ) • toE a₁ + (c 1 : ℝ) • toE a₂) :=
      eq_neg_of_add_eq_zero_right hR
    have h5 : toE x = ((c 2 : ℝ)⁻¹ * (-(c 0 : ℝ))) • toE a₁
        + ((c 2 : ℝ)⁻¹ * (-(c 1 : ℝ))) • toE a₂ := by
      have h6 : toE x = (c 2 : ℝ)⁻¹ • (-((c 0 : ℝ) • toE a₁ + (c 1 : ℝ) • toE a₂)) :=
        smul_eq_of_inv_smul h2R h4
      rw [h6]
      module
    refine hx ?_
    rw [h5]
    refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(0 : Fin 2), by simp⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(1 : Fin 2), by simp⟩))
  have hsum2 : c 0 • a₁ + c 1 • a₂ = 0 := by
    have h := hsum
    rw [hc2, zero_smul, add_zero] at h
    simpa using h
  have hpair : (∑ i : Fin 2, c (Fin.castSucc i) • (![a₁, a₂] : Fin 2 → Fin 5 → ℤ) i) = 0 := by
    rw [Fin.sum_univ_two]
    simpa using hsum2
  intro i
  fin_cases i
  · simpa using hli _ hpair 0
  · simpa using hli _ hpair 1
  · exact hc2

/-- `lam L 3` flag: `x ∈ L` of norm `< lam L 3` lies in the real span of the pair `a₁, a₂`. -/
lemma mem_realSpan_pair_of_eNorm_lt_lam3 {L : Submodule ℤ (Fin 5 → ℤ)} {a₁ a₂ x : Fin 5 → ℤ}
    (h1L : a₁ ∈ L) (h2L : a₂ ∈ L) (ha10 : a₁ ≠ 0)
    (he1 : Work.HP.eNorm a₁ ≤ Work.HP.lam L 1)
    (he2 : Work.HP.eNorm a₂ ≤ Work.HP.lam L 2)
    (hlam : Work.HP.lam L 1 ≤ Work.HP.lam L 2)
    (hli : LinearIndependent ℤ ![a₁, a₂])
    (hxL : x ∈ L) (hx : Work.HP.eNorm x < Work.HP.lam L 3) :
    toE x ∈ Submodule.span ℝ (Set.range fun i : Fin 2 => toE (![a₁, a₂] i)) := by
  by_contra hmem
  have h3 := linearIndependent_int_triple hli hmem
  have hmax : Work.HP.lam L 3 ≤
      max (max (Work.HP.eNorm a₁) (Work.HP.eNorm a₂)) (Work.HP.eNorm x) :=
    lam_le_of_norm_le (L := L) (k := 3) (f := ![a₁, a₂, x])
      (by intro j; fin_cases j <;> simp [h1L, h2L, hxL])
      h3
      (le_trans (Work.HP.eNorm_nonneg a₁) (le_trans (le_max_left _ _) (le_max_left _ _)))
      (by
        intro j
        fin_cases j
        · exact le_trans (le_max_left _ _) (le_max_left _ _)
        · exact le_trans (le_max_right _ _) (le_max_left _ _)
        · exact le_max_right _ _)
  rcases lt_or_ge (Work.HP.eNorm x) (Work.HP.lam L 2) with hlt | hge
  · obtain ⟨t, ht⟩ := exists_smul_toE_of_eNorm_lt_lam2 h1L he1 ha10 hxL hlt
    refine hmem ?_
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨![t, 0], by rw [Fin.sum_univ_two]; simpa using ht.symm⟩
  · have hmax' : max (max (Work.HP.eNorm a₁) (Work.HP.eNorm a₂)) (Work.HP.eNorm x)
        = Work.HP.eNorm x := by
      rw [max_eq_right (max_le (le_trans he1 (le_trans hlam hge)) (le_trans he2 hge))]
    rw [hmax'] at hmax
    linarith

/-- `v ∈ L` lying on the line of the shortest vector `a` is an integral multiple of `a`. -/
lemma mem_span_singleton_of_mem_realSpan {L : Submodule ℤ (Fin 5 → ℤ)} {a v : Fin 5 → ℤ}
    (haL : a ∈ L) (ha0 : a ≠ 0)
    (hshort : ∀ y ∈ L, y ≠ 0 → Work.HP.eNorm a ≤ Work.HP.eNorm y)
    (hvL : v ∈ L) (hv : toE v ∈ Submodule.span ℝ {toE a}) :
    v ∈ Submodule.span ℤ {a} := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hv
  rw [Submodule.mem_span_singleton]
  have hclose1 : (↑⌊t + 1 / 2⌋ : ℝ) - t ≤ 1 / 2 := by
    have h := Int.floor_le (t + 1 / 2)
    linarith
  have hclose2 : t - (↑⌊t + 1 / 2⌋ : ℝ) ≤ 1 / 2 := by
    have h := Int.lt_floor_add_one (t + 1 / 2)
    linarith
  have htn : t = (↑⌊t + 1 / 2⌋ : ℝ) := by
    by_contra hne
    have habs : |t - (↑⌊t + 1 / 2⌋ : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, hclose2⟩
    have hEq : toE (v - ⌊t + 1 / 2⌋ • a) = (t - (↑⌊t + 1 / 2⌋ : ℝ)) • toE a := by
      rw [map_sub, map_smul, ← Int.cast_smul_eq_zsmul ℝ ⌊t + 1 / 2⌋ (toE a), ← ht, ← sub_smul]
    have hne0 : v - ⌊t + 1 / 2⌋ • a ≠ 0 := by
      intro h0
      have h1 : (t - (↑⌊t + 1 / 2⌋ : ℝ)) • toE a = 0 := by rw [← hEq, h0, map_zero]
      rcases smul_eq_zero.mp h1 with h2 | h2
      · exact hne (by linarith)
      · exact ha0 (toE_injective (by simpa using h2))
    have hmem : v - ⌊t + 1 / 2⌋ • a ∈ L := Submodule.sub_mem _ hvL (Submodule.smul_mem _ _ haL)
    have hsh := hshort _ hmem hne0
    have hnorm : Work.HP.eNorm (v - ⌊t + 1 / 2⌋ • a)
        = |t - (↑⌊t + 1 / 2⌋ : ℝ)| * Work.HP.eNorm a := by
      rw [← norm_toE (v - ⌊t + 1 / 2⌋ • a), hEq, norm_smul, norm_toE a, Real.norm_eq_abs]
    rw [hnorm] at hsh
    nlinarith [Work.HP.eNorm_pos_of_ne_zero ha0, abs_nonneg (t - (↑⌊t + 1 / 2⌋ : ℝ)), habs]
  refine ⟨⌊t + 1 / 2⌋, ?_⟩
  apply toE_injective
  have h1 : toE v = t • toE a := ht.symm
  have h2 : t • toE a = (((⌊t + 1 / 2⌋ : ℤ)) : ℝ) • toE a := by
    conv_lhs => rw [htn]
  rw [h1, h2, map_smul, Int.cast_smul_eq_zsmul]

lemma eNorm_zsmul (k : ℤ) (v : Fin 5 → ℤ) :
    Work.HP.eNorm (k • v) = |(k : ℝ)| * Work.HP.eNorm v := by
  rw [← norm_toE (k • v), map_smul, ← Int.cast_smul_eq_zsmul ℝ k (toE v), norm_smul, norm_toE v,
    Real.norm_eq_abs]

lemma rk_span_singleton (a : Fin 5 → ℤ) (ha0 : a ≠ 0) :
    Work.HP.rk (Submodule.span ℤ ({a} : Set (Fin 5 → ℤ))) = 1 := by
  show Module.finrank ℤ (Submodule.span ℤ ({a} : Set (Fin 5 → ℤ))) = 1
  have hli : LinearIndependent ℤ (fun _ : Fin 1 => a) := by
    rw [linearIndependent_unique_iff]; exact ha0
  have h := finrank_span_eq_card hli
  have hr : (Set.range fun _ : Fin 1 => a) = ({a} : Set (Fin 5 → ℤ)) := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩
  rwa [hr] at h

set_option maxHeartbeats 800000 in
/-- A saturated rank-`2` submodule of a rank-`3` lattice is a direct summand with an
adapted `ℤ`-basis. -/
theorem exists_basis_adapted (L Λ : Submodule ℤ (Fin 5 → ℤ)) (hΛL : Λ ≤ L)
    (hsat : ∀ (x : Fin 5 → ℤ) (m : ℤ), m ≠ 0 → m • x ∈ Λ → x ∈ L → x ∈ Λ)
    (hL : Work.HP.rk L = 3) (hΛ : Work.HP.rk Λ = 2) :
    ∃ b₀ b₁ b₂ : Fin 5 → ℤ, b₀ ∈ L ∧ b₁ ∈ L ∧ b₂ ∈ L ∧
      LinearIndependent ℤ ![b₀, b₁, b₂] ∧
      L = Submodule.span ℤ ({b₀, b₁, b₂} : Set (Fin 5 → ℤ)) ∧
      Λ = Submodule.span ℤ ({b₀, b₁} : Set (Fin 5 → ℤ)) := by
  classical
  obtain ⟨n, o, hno, bO, bN, α, ha⟩ :=
    Submodule.exists_smith_normal_form_of_le (Pi.basisFun ℤ (Fin 5)) Λ L hΛL
  have hn : n = 2 := by
    have h := Module.finrank_eq_card_basis bN
    rw [Fintype.card_fin] at h
    rw [← h]; exact hΛ
  have ho : o = 3 := by
    have h := Module.finrank_eq_card_basis bO
    rw [Fintype.card_fin] at h
    rw [← h]; exact hL
  subst hn
  subst ho
  -- span descriptions of `L` and `Λ` in terms of the Smith bases
  have hLrange : L = Submodule.span ℤ (Set.range fun i : Fin 3 => ((bO i : L) : Fin 5 → ℤ)) := by
    have h : Submodule.span ℤ (Set.range bO) = ⊤ := Module.Basis.span_eq bO
    calc L = Submodule.map (Submodule.subtype L) ⊤ := by
            rw [Submodule.map_top]; exact (Submodule.range_subtype L).symm
      _ = Submodule.map (Submodule.subtype L) (Submodule.span ℤ (Set.range bO)) := by rw [h]
      _ = Submodule.span ℤ (Submodule.subtype L '' Set.range bO) := Submodule.map_span _ _
      _ = Submodule.span ℤ (Set.range fun i : Fin 3 => ((bO i : L) : Fin 5 → ℤ)) := by
            rw [← Set.range_comp]; rfl
  have hΛrange : Λ = Submodule.span ℤ (Set.range fun i : Fin 2 => ((bN i : Λ) : Fin 5 → ℤ)) := by
    have h : Submodule.span ℤ (Set.range bN) = ⊤ := Module.Basis.span_eq bN
    calc Λ = Submodule.map (Submodule.subtype Λ) ⊤ := by
            rw [Submodule.map_top]; exact (Submodule.range_subtype Λ).symm
      _ = Submodule.map (Submodule.subtype Λ) (Submodule.span ℤ (Set.range bN)) := by rw [h]
      _ = Submodule.span ℤ (Submodule.subtype Λ '' Set.range bN) := Submodule.map_span _ _
      _ = Submodule.span ℤ (Set.range fun i : Fin 2 => ((bN i : Λ) : Fin 5 → ℤ)) := by
            rw [← Set.range_comp]; rfl
  -- `bO i ∈ Λ` for `i : Fin 2` by saturation
  have hmem : ∀ i : Fin 2, ((bO (Fin.castLE hno i) : L) : Fin 5 → ℤ) ∈ Λ := by
    intro i
    have hne : α i ≠ 0 := by
      intro h0
      have h1 : (bN i : Fin 5 → ℤ) = 0 := by rw [ha i, h0, zero_smul]
      exact bN.ne_zero i (Subtype.ext h1)
    refine hsat _ (α i) hne ?_ (bO (Fin.castLE hno i)).2
    show α i • ((bO (Fin.castLE hno i) : L) : Fin 5 → ℤ) ∈ Λ
    rw [← ha i]
    exact (bN i).2
  have hc0 : Fin.castLE hno (0 : Fin 2) = (0 : Fin 3) := Fin.ext rfl
  have hc1 : Fin.castLE hno (1 : Fin 2) = (1 : Fin 3) := Fin.ext rfl
  have hspanΛ : Λ = Submodule.span ℤ ({(bO (0 : Fin 3) : Fin 5 → ℤ),
      (bO (1 : Fin 3) : Fin 5 → ℤ)} : Set (Fin 5 → ℤ)) := by
    rw [← hc0, ← hc1]
    refine le_antisymm ?_ ?_
    · rw [hΛrange]
      refine Submodule.span_le.mpr ?_
      rintro x ⟨i, rfl⟩
      have hbo : α i • ((bO (Fin.castLE hno i) : L) : Fin 5 → ℤ) ∈ Submodule.span ℤ
          ({(bO (0 : Fin 3) : Fin 5 → ℤ), (bO (1 : Fin 3) : Fin 5 → ℤ)} : Set (Fin 5 → ℤ)) :=
        Submodule.smul_mem _ _ (by fin_cases i <;> exact Submodule.subset_span (by simp))
      show (bN i : Fin 5 → ℤ) ∈ Submodule.span ℤ
        ({(bO (0 : Fin 3) : Fin 5 → ℤ), (bO (1 : Fin 3) : Fin 5 → ℤ)} : Set (Fin 5 → ℤ))
      rw [ha i]
      exact hbo
    · rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · exact hmem 0
      · exact hmem 1
  refine ⟨(bO (0 : Fin 3) : Fin 5 → ℤ), (bO (1 : Fin 3) : Fin 5 → ℤ), (bO (2 : Fin 3) : Fin 5 → ℤ),
    (bO 0).2, (bO 1).2, (bO 2).2, ?_, ?_, hspanΛ⟩
  · have h : LinearIndependent ℤ (fun i : Fin 3 => ((bO i : L) : Fin 5 → ℤ)) :=
      bO.linearIndependent.map' (Submodule.subtype L) (Submodule.ker_subtype L)
    convert h using 1
    ext i
    fin_cases i <;> rfl
  · refine le_antisymm ?_ ?_
    · refine hLrange.le.trans (Submodule.span_mono ?_)
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rw [Submodule.span_le]
      rintro x (rfl | rfl | rfl)
      · exact (bO 0).2
      · exact (bO 1).2
      · exact (bO 2).2


lemma range_pair (x y : Fin 5 → ℤ) :
    (Set.range (![x, y] : Fin 2 → (Fin 5 → ℤ))) = ({x, y} : Set (Fin 5 → ℤ)) := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- The integer points of the real span of a lattice form its saturation. -/
lemma mem_satLat_of_mem_realSpan {Λ : Submodule ℤ (Fin 5 → ℤ)} {x : Fin 5 → ℤ}
    (hx : toE x ∈ Submodule.span ℝ (ΛE Λ : Set E5)) : x ∈ Work.HP.satLat Λ := by
  rw [← Work.HP.numaux.doubleOrth_eq_satLat Λ, Work.HP.mem_orthLat]
  intro a ha
  have hinner : inner ℝ (toE a) (toE x) = 0 := by
    refine Submodule.span_induction (p := fun y _ => inner ℝ (toE a) y = 0) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨l, hl, rfl⟩
      rw [inner_toE]
      have h2 : Work.HP.dotI a l = 0 := ha l hl
      have h3 : ((Work.HP.dotI a l : ℤ) : ℝ) = 0 := by rw [h2]; norm_num
      simpa only [Work.HP.dotI, Int.cast_sum, Int.cast_mul] using h3
    · simp
    · intro y z hy hz ihy ihz
      rw [inner_add_right, ihy, ihz, add_zero]
    · intro c y hy ihy
      rw [inner_smul_right, ihy, mul_zero]
  have h3 : ((Work.HP.dotI x a : ℤ) : ℝ) = 0 := by
    have h4 : ((Work.HP.dotI x a : ℤ) : ℝ) = inner ℝ (toE a) (toE x) := by
      rw [Work.HP.dotI_comm]
      simp only [Work.HP.dotI, Int.cast_sum, Int.cast_mul, inner_toE]
    rw [h4, hinner]
  exact Int.cast_eq_zero.mp h3

/-- The rank of `satLat S ⊓ L` is at most the rank of `S`. -/
lemma rk_satLat_inf_le (L S : Submodule ℤ (Fin 5 → ℤ)) :
    Work.HP.rk (Work.HP.satLat S ⊓ L) ≤ Work.HP.rk S :=
  (Submodule.finrank_mono inf_le_left).trans_eq (Work.HP.numaux.rk_satLat S)

/-- The rank of `span{a₁,a₂}` is `2`. -/
lemma rk_span_pair {a₁ a₂ : Fin 5 → ℤ} (ha : LinearIndependent ℤ ![a₁, a₂]) :
    Work.HP.rk (Submodule.span ℤ ({a₁, a₂} : Set (Fin 5 → ℤ))) = 2 := by
  have h := Work.HP.numaux.rk_span_eq (ι := Fin 5) (r := 2) ha
  rwa [range_pair] at h

/-- The rank of `span{a}` is `1`. -/
lemma rk_span_one {a : Fin 5 → ℤ} (ha0 : a ≠ 0) :
    Work.HP.rk (Submodule.span ℤ ({a} : Set (Fin 5 → ℤ))) = 1 :=
  rk_span_singleton a ha0

set_option maxHeartbeats 800000 in
/-- A saturated rank-`1` submodule of a rank-`2` lattice is a direct summand with an
adapted `ℤ`-basis. -/
theorem exists_basis_adapted_dim1 (M Λ : Submodule ℤ (Fin 5 → ℤ)) (hΛM : Λ ≤ M)
    (hsat : ∀ (x : Fin 5 → ℤ) (m : ℤ), m ≠ 0 → m • x ∈ Λ → x ∈ M → x ∈ Λ)
    (hM : Work.HP.rk M = 2) (hΛ : Work.HP.rk Λ = 1) :
    ∃ c₀ c₁ : Fin 5 → ℤ, c₀ ∈ M ∧ c₁ ∈ M ∧ LinearIndependent ℤ ![c₀, c₁] ∧
      M = Submodule.span ℤ ({c₀, c₁} : Set (Fin 5 → ℤ)) ∧
      Λ = Submodule.span ℤ ({c₀} : Set (Fin 5 → ℤ)) := by
  classical
  obtain ⟨n, o, hno, bO, bN, α, ha⟩ :=
    Submodule.exists_smith_normal_form_of_le (Pi.basisFun ℤ (Fin 5)) Λ M hΛM
  have hn : n = 1 := by
    have h := Module.finrank_eq_card_basis bN
    rw [Fintype.card_fin] at h
    rw [← h]; exact hΛ
  have ho : o = 2 := by
    have h := Module.finrank_eq_card_basis bO
    rw [Fintype.card_fin] at h
    rw [← h]; exact hM
  subst hn
  subst ho
  have hΛrange : Λ = Submodule.span ℤ (Set.range fun i : Fin 1 => ((bN i : Λ) : Fin 5 → ℤ)) := by
    have h : Submodule.span ℤ (Set.range bN) = ⊤ := Module.Basis.span_eq bN
    calc Λ = Submodule.map (Submodule.subtype Λ) ⊤ := by
            rw [Submodule.map_top]; exact (Submodule.range_subtype Λ).symm
      _ = Submodule.map (Submodule.subtype Λ) (Submodule.span ℤ (Set.range bN)) := by rw [h]
      _ = Submodule.span ℤ (Submodule.subtype Λ '' Set.range bN) := Submodule.map_span _ _
      _ = Submodule.span ℤ (Set.range fun i : Fin 1 => ((bN i : Λ) : Fin 5 → ℤ)) := by
            rw [← Set.range_comp]; rfl
  have hmem : ((bO (0 : Fin 2) : M) : Fin 5 → ℤ) ∈ Λ := by
    have hne : α (0 : Fin 1) ≠ 0 := by
      intro h0
      have h1 : (bN (0 : Fin 1) : Fin 5 → ℤ) = 0 := by rw [ha 0, h0, zero_smul]
      exact bN.ne_zero 0 (Subtype.ext h1)
    refine hsat _ (α (0 : Fin 1)) hne ?_ (bO (0 : Fin 2)).2
    show α (0 : Fin 1) • ((bO (Fin.castLE hno (0 : Fin 1)) : M) : Fin 5 → ℤ) ∈ Λ
    rw [← ha 0]
    exact (bN 0).2
  have hrel : α (0 : Fin 1) • (bO (0 : Fin 2) : Fin 5 → ℤ) = (bN (0 : Fin 1) : Fin 5 → ℤ) := by
    have h := (ha 0).symm
    rwa [show Fin.castLE hno (0 : Fin 1) = (0 : Fin 2) from Fin.ext rfl] at h
  have hspanΛ : Λ = Submodule.span ℤ ({(bO (0 : Fin 2) : Fin 5 → ℤ)} : Set (Fin 5 → ℤ)) := by
    refine le_antisymm ?_ ?_
    · rw [hΛrange, Submodule.span_le]
      rintro x ⟨i, rfl⟩
      fin_cases i
      show (bN (0 : Fin 1) : Fin 5 → ℤ) ∈
        Submodule.span ℤ ({(bO (0 : Fin 2) : Fin 5 → ℤ)} : Set (Fin 5 → ℤ))
      rw [hrel.symm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      rintro x rfl
      exact hmem
  have hspanM : M = Submodule.span ℤ ({(bO (0 : Fin 2) : Fin 5 → ℤ),
      (bO (1 : Fin 2) : Fin 5 → ℤ)} : Set (Fin 5 → ℤ)) := by
    have hMrange : M = Submodule.span ℤ (Set.range fun i : Fin 2 => ((bO i : M) : Fin 5 → ℤ)) := by
      have h : Submodule.span ℤ (Set.range bO) = ⊤ := Module.Basis.span_eq bO
      calc M = Submodule.map (Submodule.subtype M) ⊤ := by
              rw [Submodule.map_top]; exact (Submodule.range_subtype M).symm
        _ = Submodule.map (Submodule.subtype M) (Submodule.span ℤ (Set.range bO)) := by rw [h]
        _ = Submodule.span ℤ (Submodule.subtype M '' Set.range bO) := Submodule.map_span _ _
        _ = Submodule.span ℤ (Set.range fun i : Fin 2 => ((bO i : M) : Fin 5 → ℤ)) := by
              rw [← Set.range_comp]; rfl
    refine le_antisymm ?_ ?_
    · refine hMrange.le.trans (Submodule.span_mono ?_)
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · exact (bO 0).2
      · exact (bO 1).2
  have hli : LinearIndependent ℤ ![(bO (0 : Fin 2) : Fin 5 → ℤ), (bO (1 : Fin 2) : Fin 5 → ℤ)] := by
    have h : LinearIndependent ℤ (fun i : Fin 2 => ((bO i : M) : Fin 5 → ℤ)) :=
      bO.linearIndependent.map' (Submodule.subtype M) (Submodule.ker_subtype M)
    convert h using 1
    ext i
    fin_cases i <;> rfl
  exact ⟨(bO (0 : Fin 2) : Fin 5 → ℤ), (bO (1 : Fin 2) : Fin 5 → ℤ), (bO 0).2, (bO 1).2,
    hli, hspanM, hspanΛ⟩


lemma range_triple (x y z : Fin 5 → ℤ) :
    (Set.range (![x, y, z] : Fin 3 → (Fin 5 → ℤ))) = ({x, y, z} : Set (Fin 5 → ℤ)) := by
  ext w
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

set_option maxHeartbeats 1000000 in
/-- A `ℤ`-basis `b₀,b₁,b₂` of a rank-`3` lattice adapted to the flag of the successive
minima. -/
theorem exists_flagBasis (L : Submodule ℤ (Fin 5 → ℤ)) (hL : Work.HP.rk L = 3) :
    ∃ b : Fin 3 → (Fin 5 → ℤ),
      LinearIndependent ℤ b ∧ L = Submodule.span ℤ (Set.range b) ∧
      (∀ v ∈ L, Work.HP.eNorm v < Work.HP.lam L 2 → ∃ c : Fin 3 → ℤ,
        v = ∑ i, c i • b i ∧ c 1 = 0 ∧ c 2 = 0) ∧
      (∀ v ∈ L, Work.HP.eNorm v < Work.HP.lam L 3 → ∃ c : Fin 3 → ℤ,
        v = ∑ i, c i • b i ∧ c 2 = 0) := by
  classical
  -- two short independent vectors
  obtain ⟨f, hfL, hfli, hfn⟩ := Work.HP.numaux.lam_attained (ι := Fin 5) L (j := 1) (by omega)
  obtain ⟨g, hgL, hgli, hgn⟩ := Work.HP.numaux.lam_attained (ι := Fin 5) L (j := 2) (by omega)
  obtain ⟨t, htli⟩ := snoc_linIndep hfli hgli
  set a₁ : Fin 5 → ℤ := f 0 with ha₁
  set a₂ : Fin 5 → ℤ := g t with ha₂
  have ha₁L : a₁ ∈ L := hfL 0
  have ha₂L : a₂ ∈ L := hgL t
  have hsnoc : (Fin.snoc f (g t) : Fin 2 → (Fin 5 → ℤ)) = ![a₁, a₂] := by
    funext i
    fin_cases i
    · exact ha₁.symm
    · exact ha₂.symm
  have hli : LinearIndependent ℤ ![a₁, a₂] := hsnoc ▸ htli
  have he₁ : Work.HP.eNorm a₁ ≤ Work.HP.lam L 1 := hfn 0
  have he₂ : Work.HP.eNorm a₂ ≤ Work.HP.lam L 2 := hgn t
  have ha₁0 : a₁ ≠ 0 := hfli.ne_zero 0
  -- the saturated rank-1 and rank-2 submodules
  set S₁ : Submodule ℤ (Fin 5 → ℤ) := Submodule.span ℤ ({a₁} : Set (Fin 5 → ℤ)) with hS₁
  set S₂ : Submodule ℤ (Fin 5 → ℤ) := Submodule.span ℤ ({a₁, a₂} : Set (Fin 5 → ℤ)) with hS₂
  set Λ₁ : Submodule ℤ (Fin 5 → ℤ) := Work.HP.satLat S₁ ⊓ L with hΛ₁
  set Λ₂ : Submodule ℤ (Fin 5 → ℤ) := Work.HP.satLat S₂ ⊓ L with hΛ₂
  have ha₁S₁ : a₁ ∈ S₁ := by rw [hS₁]; exact Submodule.subset_span (by simp)
  have ha₁S₂ : a₁ ∈ S₂ := by rw [hS₂]; exact Submodule.subset_span (by simp)
  have ha₂S₂ : a₂ ∈ S₂ := by rw [hS₂]; exact Submodule.subset_span (by simp)
  have ha₁Λ₁ : a₁ ∈ Λ₁ := ⟨Work.HP.le_satLat S₁ ha₁S₁, ha₁L⟩
  have ha₁Λ₂ : a₁ ∈ Λ₂ := ⟨Work.HP.le_satLat S₂ ha₁S₂, ha₁L⟩
  have ha₂Λ₂ : a₂ ∈ Λ₂ := ⟨Work.HP.le_satLat S₂ ha₂S₂, ha₂L⟩
  have hS₁S₂ : S₁ ≤ S₂ := by
    rw [hS₁, hS₂, Submodule.span_le]
    rintro x rfl
    exact Submodule.subset_span (by simp)
  have hΛ₁le₂ : Λ₁ ≤ Λ₂ := by
    rw [hΛ₁, hΛ₂]
    exact le_inf (inf_le_left.trans (Work.HP.satLat_mono hS₁S₂)) inf_le_right
  have hΛ₂rk : Work.HP.rk Λ₂ = 2 := by
    have hle : S₂ ≤ Λ₂ := le_inf (Work.HP.le_satLat S₂) (by
      rw [hS₂, Submodule.span_le]
      rintro x (rfl | rfl)
      · exact ha₁L
      · exact ha₂L)
    have h2 : Work.HP.rk S₂ ≤ Work.HP.rk Λ₂ := Submodule.finrank_mono hle
    have h3 : Work.HP.rk S₂ = 2 := by rw [hS₂]; exact rk_span_pair hli
    have h4 : Work.HP.rk Λ₂ ≤ Work.HP.rk S₂ := by
      have h := rk_satLat_inf_le L S₂
      rwa [← hΛ₂] at h
    omega
  have hΛ₁rk : Work.HP.rk Λ₁ = 1 := by
    have hle : S₁ ≤ Λ₁ := le_inf (Work.HP.le_satLat S₁) (by
      rw [hS₁, Submodule.span_le]
      rintro x rfl
      exact ha₁L)
    have h2 : Work.HP.rk S₁ ≤ Work.HP.rk Λ₁ := Submodule.finrank_mono hle
    have h3 : Work.HP.rk S₁ = 1 := by rw [hS₁]; exact rk_span_one ha₁0
    have h4 : Work.HP.rk Λ₁ ≤ Work.HP.rk S₁ := by
      have h := rk_satLat_inf_le L S₁
      rwa [← hΛ₁] at h
    omega
  -- saturation statements
  have hsat₂ : ∀ (x : Fin 5 → ℤ) (m : ℤ), m ≠ 0 → m • x ∈ Λ₂ → x ∈ L → x ∈ Λ₂ := by
    intro x m hm hmx hxL
    rw [hΛ₂] at hmx ⊢
    obtain ⟨h1, -⟩ := hmx
    obtain ⟨k, hk, hk1⟩ := Work.HP.mem_satLat.mp h1
    exact ⟨⟨k * m, mul_ne_zero hk hm, by rw [mul_smul]; exact hk1⟩, hxL⟩
  have hsat₁ : ∀ (x : Fin 5 → ℤ) (m : ℤ), m ≠ 0 → m • x ∈ Λ₁ → x ∈ L → x ∈ Λ₁ := by
    intro x m hm hmx hxL
    rw [hΛ₁] at hmx ⊢
    obtain ⟨h1, -⟩ := hmx
    obtain ⟨k, hk, hk1⟩ := Work.HP.mem_satLat.mp h1
    exact ⟨⟨k * m, mul_ne_zero hk hm, by rw [mul_smul]; exact hk1⟩, hxL⟩
  have hsat₁₂ : ∀ (x : Fin 5 → ℤ) (m : ℤ), m ≠ 0 → m • x ∈ Λ₁ → x ∈ Λ₂ → x ∈ Λ₁ := by
    intro x m hm hmx hxΛ₂
    have hxL : x ∈ L := by
      rw [hΛ₂] at hxΛ₂
      exact hxΛ₂.2
    exact hsat₁ x m hm hmx hxL
  -- adapted bases
  obtain ⟨e₀, e₁, e₂, he₀L, he₁L, he₂L, heli, hespan, hΛ₂spanE⟩ :=
    exists_basis_adapted L Λ₂ (by rw [hΛ₂]; exact inf_le_right) hsat₂ hL hΛ₂rk
  obtain ⟨c₀, c₁, hc₀Λ₂, hc₁Λ₂, hcli, hΛ₂spanC, hΛ₁spanC⟩ :=
    exists_basis_adapted_dim1 Λ₂ Λ₁ hΛ₁le₂ hsat₁₂ hΛ₂rk hΛ₁rk
  have he₀Λ₂ : e₀ ∈ Λ₂ := by rw [hΛ₂spanE]; exact Submodule.subset_span (by simp)
  have he₁Λ₂ : e₁ ∈ Λ₂ := by rw [hΛ₂spanE]; exact Submodule.subset_span (by simp)
  -- the final basis
  have hspan : L = Submodule.span ℤ ({c₀, c₁, e₂} : Set (Fin 5 → ℤ)) := by
    have h1 : L = Λ₂ ⊔ Submodule.span ℤ ({e₂} : Set (Fin 5 → ℤ)) := by
      rw [hespan, hΛ₂spanE, ← Submodule.span_union]
      congr 1
      ext x
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [h1, hΛ₂spanC, ← Submodule.span_union]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hbli : LinearIndependent ℤ ![c₀, c₁, e₂] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum : c 0 • c₀ + c 1 • c₁ + c 2 • e₂ = 0 := by
      have h := hc; rw [Fin.sum_univ_three] at h; simpa using h
    have hc2 : c 2 = 0 := by
      by_contra h2
      have he₂Λ₂ : e₂ ∈ Λ₂ := by
        refine hsat₂ e₂ (c 2) h2 ?_ he₂L
        have h3 : c 2 • e₂ = -(c 0 • c₀ + c 1 • c₁) := eq_neg_of_add_eq_zero_right hsum
        rw [h3]
        exact Submodule.neg_mem _ (add_mem (Submodule.smul_mem _ _ hc₀Λ₂) (Submodule.smul_mem _ _ hc₁Λ₂))
      have : e₂ ∈ Submodule.span ℤ ({e₀, e₁} : Set (Fin 5 → ℤ)) := by
        rw [← hΛ₂spanE]; exact he₂Λ₂
      rw [Submodule.mem_span_pair] at this
      obtain ⟨p, q, hpq⟩ := this
      have hrel : p • e₀ + q • e₁ + (-1) • e₂ = 0 := by
        rw [neg_one_smul, ← hpq, add_neg_cancel]
      have hcontra := (Fintype.linearIndependent_iff.mp heli) (![p, q, -1] : Fin 3 → ℤ) (by
        rw [Fin.sum_univ_three]
        simpa using hrel) 2
      norm_num at hcontra
    have hsum' : c 0 • c₀ + c 1 • c₁ = 0 := by
      rw [hc2, zero_smul, add_zero] at hsum
      simpa using hsum
    have hpair : (∑ i : Fin 2, (![c 0, c 1] : Fin 2 → ℤ) i • (![c₀, c₁] : Fin 2 → (Fin 5 → ℤ)) i) = 0 := by
      rw [Fin.sum_univ_two]
      simpa using hsum'
    have hzeros := (Fintype.linearIndependent_iff.mp hcli) (![c 0, c 1] : Fin 2 → ℤ) hpair
    intro i
    fin_cases i
    · simpa using hzeros 0
    · simpa using hzeros 1
    · exact hc2
  -- the flags
  refine ⟨![c₀, c₁, e₂], hbli, ?_, ?_, ?_⟩
  · rw [range_triple]; exact hspan
  · intro v hvL hv
    have hshort : ∀ y ∈ L, y ≠ 0 → Work.HP.eNorm a₁ ≤ Work.HP.eNorm y := fun y hy hy0 =>
      le_trans he₁ (Work.HP.lam_one_le_eNorm L hy hy0)
    obtain ⟨s, hs⟩ := exists_smul_toE_of_eNorm_lt_lam2 ha₁L he₁ ha₁0 hvL hv
    have hmem : toE v ∈ Submodule.span ℝ ({toE a₁} : Set E5) :=
      Submodule.mem_span_singleton.mpr ⟨s, hs.symm⟩
    have hva : v ∈ Submodule.span ℤ ({a₁} : Set (Fin 5 → ℤ)) :=
      mem_span_singleton_of_mem_realSpan ha₁L ha₁0 hshort hvL hmem
    have hvS₁ : v ∈ S₁ := by rw [hS₁]; exact hva
    have hvΛ₁ : v ∈ Λ₁ := ⟨Work.HP.le_satLat S₁ hvS₁, hvL⟩
    have hvspan : v ∈ Submodule.span ℤ ({c₀} : Set (Fin 5 → ℤ)) := by
      rw [← hΛ₁spanC]; exact hvΛ₁
    rw [Submodule.mem_span_singleton] at hvspan
    obtain ⟨α, hα⟩ := hvspan
    refine ⟨![α, 0, 0], ?_, by simp, by simp⟩
    rw [Fin.sum_univ_three]
    simp [hα]
  · intro v hvL hv
    have hrangeE : (Set.range fun i : Fin 2 => toE (![a₁, a₂] i)) = ({toE a₁, toE a₂} : Set E5) := by
      ext y
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    have hreal0 := mem_realSpan_pair_of_eNorm_lt_lam3 ha₁L ha₂L ha₁0 he₁ he₂
      (Work.HP.lam_mono L (by norm_num) (by omega)) hli hvL hv
    have hreal : toE v ∈ Submodule.span ℝ ({toE a₁, toE a₂} : Set E5) := by
      rwa [hrangeE] at hreal0
    have hEq : Submodule.span ℝ (ΛE S₂ : Set E5)
        = Submodule.span ℝ ({toE a₁, toE a₂} : Set E5) := by
      refine le_antisymm ?_ ?_
      · rw [Submodule.span_le]
        rintro y ⟨l, hl, rfl⟩
        have hl' : l ∈ Submodule.span ℤ ({a₁, a₂} : Set (Fin 5 → ℤ)) := by rw [← hS₂]; exact hl
        obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hl'
        refine Submodule.mem_span_pair.mpr ⟨(p : ℝ), (q : ℝ), ?_⟩
        rw [← hpq, map_add, map_smul, map_smul, Int.cast_smul_eq_zsmul ℝ p (toE a₁),
          Int.cast_smul_eq_zsmul ℝ q (toE a₂)]
      · rw [Submodule.span_le]
        rintro y (rfl | rfl)
        · exact Submodule.subset_span ⟨a₁, ha₁S₂, rfl⟩
        · exact Submodule.subset_span ⟨a₂, ha₂S₂, rfl⟩
    have hreal' : toE v ∈ Submodule.span ℝ (ΛE S₂ : Set E5) := by
      rw [← hEq] at hreal
      exact hreal
    have hvΛ₂ : v ∈ Λ₂ := ⟨mem_satLat_of_mem_realSpan hreal', hvL⟩
    have hvspan : v ∈ Submodule.span ℤ ({c₀, c₁} : Set (Fin 5 → ℤ)) := by
      rw [← hΛ₂spanC]; exact hvΛ₂
    obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hvspan
    refine ⟨![p, q, 0], ?_, by simp⟩
    have hsum : (∑ i, (![p, q, 0] : Fin 3 → ℤ) i
        • (![c₀, c₁, e₂] : Fin 3 → (Fin 5 → ℤ)) i) = p • c₀ + q • c₁ := by
      rw [Fin.sum_univ_three]
      simp
    rw [hsum, hpq]


lemma kill_At (L : Submodule ℤ (Fin 5 → ℤ)) (hL : Work.HP.rk L = 3) (T : ℝ)
    (hT : 0 ≤ T) (b : Fin 3 → (Fin 5 → ℤ)) (hli : LinearIndependent ℤ b)
    (hbasis : L = Submodule.span ℤ (Set.range b))
    (hflag2 : ∀ v ∈ L, Work.HP.eNorm v < Work.HP.lam L 2 → ∃ c : Fin 3 → ℤ,
      v = ∑ i, c i • b i ∧ c 1 = 0 ∧ c 2 = 0)
    (hflag3 : ∀ v ∈ L, Work.HP.eNorm v < Work.HP.lam L 3 → ∃ c : Fin 3 → ℤ,
      v = ∑ i, c i • b i ∧ c 2 = 0)
    (m : Fin 3 → ℕ) (hmp : ∀ k : Fin 3, 0 < m k) (hdvd : ∀ i j : Fin 3, i ≤ j → m j ∣ m i)
    (hbig : ∀ k : Fin 3, 2 * T < (m k : ℝ) * Work.HP.lam L (k.val + 1))
    {g : Fin 5 → ℤ} (hg : g ∈ Submodule.span ℤ (Set.range fun i : Fin 3 => (m i : ℤ) • b i))
    (hgle : Work.HP.eNorm g ≤ 2 * T) : g = 0 := by
  classical
  by_contra hg0
  rw [Submodule.mem_span_range_iff_exists_fun] at hg
  obtain ⟨z, hz⟩ := hg
  have hz0 : z ≠ 0 := by
    intro hz00
    refine hg0 ?_
    have h : (∑ i, z i • ((m i : ℤ) • b i)) = 0 := by rw [hz00]; simp
    rwa [hz] at h
  have hne : (Finset.univ.filter (fun i : Fin 3 => z i ≠ 0)).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz0
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨k, hkmem, hkmax⟩ :=
    Finset.exists_max_image (Finset.univ.filter (fun i : Fin 3 => z i ≠ 0))
      (fun i : Fin 3 => i.val) hne
  have hkne : z k ≠ 0 := (Finset.mem_filter.mp hkmem).2
  have hkzero : ∀ j : Fin 3, k < j → z j = 0 := by
    intro j hj
    by_contra hjn
    have hjm : j ∈ Finset.univ.filter (fun i : Fin 3 => z i ≠ 0) := by simp [hjn]
    have := hkmax j hjm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hkmem
    omega
  let c : Fin 3 → ℤ := fun i => if i.val ≤ k.val then z i * ((m i / m k : ℕ) : ℤ) else 0
  let w : Fin 5 → ℤ := ∑ i, c i • b i
  have hwdef : w = ∑ i, c i • b i := rfl
  have hwL : w ∈ L := by
    rw [hbasis, Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, hwdef⟩
  have hck : c k = z k := by
    simp only [c, if_pos (le_refl k.val)]
    have h1 : (m k / m k : ℕ) = 1 := Nat.div_self (hmp k)
    rw [h1]
    push_cast
    ring
  have hmw : (m k : ℤ) • w = g := by
    have h1 : (m k : ℤ) • w = ∑ i, ((m k : ℤ) * c i) • b i := by
      rw [hwdef, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
    have h2 : ∀ i : Fin 3, (m k : ℤ) * c i = z i * (m i : ℤ) := by
      intro i
      by_cases hi : i.val ≤ k.val
      · have hci : c i = z i * ((m i / m k : ℕ) : ℤ) := by simp only [c, if_pos hi]
        have hmi : ((m i : ℕ) : ℤ) = (m k : ℤ) * ((m i / m k : ℕ) : ℤ) := by
          have h1 : (m i / m k) * m k = m i := Nat.div_mul_cancel (hdvd i k hi)
          calc ((m i : ℕ) : ℤ) = (((m i / m k) * m k : ℕ) : ℤ) := by rw [h1]
            _ = ((m i / m k : ℕ) : ℤ) * (m k : ℤ) := by rw [Nat.cast_mul]
            _ = (m k : ℤ) * ((m i / m k : ℕ) : ℤ) := by ring
        rw [hci, hmi]
        ring
      · have hci : c i = 0 := by simp only [c, if_neg hi]
        have hik : k < i := by omega
        rw [hci, mul_zero, hkzero i hik, zero_mul]
    have h3 : (∑ i, (z i * (m i : ℤ)) • b i) = g := by
      rw [← hz]
      exact Finset.sum_congr rfl fun i _ => (smul_smul _ _ _).symm
    rw [h1]
    exact (Finset.sum_congr rfl fun i _ => by rw [h2 i]).trans h3
  have hnorm : Work.HP.eNorm w < Work.HP.lam L (k.val + 1) := by
    have hmkpos : (0 : ℝ) < (m k : ℝ) := by exact_mod_cast hmp k
    have h1 : Work.HP.eNorm g = (m k : ℝ) * Work.HP.eNorm w := by
      have h := congrArg Work.HP.eNorm hmw
      rw [eNorm_zsmul] at h
      have habs : |(((m k : ℤ)) : ℝ)| = (m k : ℝ) := by
        rw [show (((m k : ℤ)) : ℝ) = ((m k : ℕ) : ℝ) from by simp]
        exact abs_of_nonneg (Nat.cast_nonneg _)
      rw [habs] at h
      exact h.symm
    have h2 : (m k : ℝ) * Work.HP.eNorm w ≤ 2 * T := by linarith
    have h4 := hbig k
    nlinarith [h2, h4, hmkpos]
  have huniq : ∀ v v' : Fin 3 → ℤ, (∑ i, v i • b i) = (∑ i, v' i • b i) → v = v' := by
    intro v v' hv
    have hsum : (∑ i, (v i - v' i) • b i) = 0 := by
      rw [Finset.sum_congr rfl (fun i _ => sub_smul (v i) (v' i) (b i)), Finset.sum_sub_distrib,
        hv, sub_self]
    have hzero := (Fintype.linearIndependent_iff.mp hli) (fun i => v i - v' i) hsum
    funext i
    have := hzero i
    omega
  have hwne : w ≠ 0 := by
    intro h0
    have h1 : c = 0 := by
      apply huniq c 0
      rw [← hwdef, h0]
      simp
    exact hkne (hck ▸ congrFun h1 k)
  have hkval : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by have := k.isLt; omega
  rcases hkval with hk | hk | hk
  · have hk' : k = (0 : Fin 3) := Fin.ext hk
    subst hk'
    simp only [Fin.val_zero, zero_add] at hnorm
    have h1 : Work.HP.lam L 1 ≤ Work.HP.eNorm w := Work.HP.lam_one_le_eNorm L hwL hwne
    linarith
  · have hk' : k = (1 : Fin 3) := Fin.ext hk
    subst hk'
    simp only [Fin.val_one, Nat.reduceAdd] at hnorm
    obtain ⟨c', hc', hc'1, -⟩ := hflag2 w hwL hnorm
    have hcc : c = c' := huniq c c' (by rw [← hwdef, hc'])
    have h1 : c 1 = 0 := by rw [hcc, hc'1]
    rw [hck] at h1
    exact hkne (by simpa using h1)
  · have hk' : k = (2 : Fin 3) := Fin.ext hk
    subst hk'
    simp only [Fin.val_two, Nat.reduceAdd] at hnorm
    obtain ⟨c', hc', hc'2⟩ := hflag3 w hwL hnorm
    have hcc : c = c' := huniq c c' (by rw [← hwdef, hc'])
    have h1 : c 2 = 0 := by rw [hcc, hc'2]
    rw [hck] at h1
    exact hkne (by simpa using h1)


theorem ballCount_le_of_basis (L : Submodule ℤ (Fin 5 → ℤ)) (hL : Work.HP.rk L = 3) (T : ℝ)
    (hT : 0 ≤ T) (b : Fin 3 → (Fin 5 → ℤ)) (hli : LinearIndependent ℤ b)
    (hbasis : L = Submodule.span ℤ (Set.range b))
    (hflag2 : ∀ v ∈ L, Work.HP.eNorm v < Work.HP.lam L 2 → ∃ c : Fin 3 → ℤ,
      v = ∑ i, c i • b i ∧ c 1 = 0 ∧ c 2 = 0)
    (hflag3 : ∀ v ∈ L, Work.HP.eNorm v < Work.HP.lam L 3 → ∃ c : Fin 3 → ℤ,
      v = ∑ i, c i • b i ∧ c 2 = 0) :
    (Work.HP.ballCount L T : ℝ) ≤ 27 * ∏ j : Fin 3, (1 + T / Work.HP.lam L (j.val + 1)) := by
  classical
  have hL1 : 0 < Work.HP.lam L 1 := Work.HP.lam_pos L le_rfl (by omega)
  have hL2 : 0 < Work.HP.lam L 2 := Work.HP.lam_pos L (by norm_num) (by omega)
  have hL3 : 0 < Work.HP.lam L 3 := Work.HP.lam_pos L (by norm_num) (by omega)
  have h12 : Work.HP.lam L 1 ≤ Work.HP.lam L 2 := Work.HP.lam_mono L (by norm_num) (by omega)
  have h23 : Work.HP.lam L 2 ≤ Work.HP.lam L 3 := Work.HP.lam_mono L (by norm_num) (by omega)
  obtain ⟨m1, m2, m3, hm1, hm2, hm3, hd32, hd21, hlt1, hlt2, hlt3, hprod⟩ :=
    exists_chain3 (x1 := T / Work.HP.lam L 1) (x2 := T / Work.HP.lam L 2)
      (x3 := T / Work.HP.lam L 3) (div_nonneg hT hL1.le)
      (by rw [div_le_div_iff₀ hL2 hL1]; exact mul_le_mul_of_nonneg_left h12 hT)
      (by rw [div_le_div_iff₀ hL3 hL2]; exact mul_le_mul_of_nonneg_left h23 hT)
      (div_nonneg hT hL3.le)
  let m : Fin 3 → ℕ := ![m1, m2, m3]
  have hm0 : m (0 : Fin 3) = m1 := by simp [m]
  have hm1v : m (1 : Fin 3) = m2 := by simp [m]
  have hm2v : m (2 : Fin 3) = m3 := by simp [m]
  have hmp : ∀ k : Fin 3, 0 < m k := by
    intro k
    fin_cases k
    · show 0 < m (0 : Fin 3); rw [hm0]; exact hm1
    · show 0 < m (1 : Fin 3); rw [hm1v]; exact hm2
    · show 0 < m (2 : Fin 3); rw [hm2v]; exact hm3
  have hdvd : ∀ i j : Fin 3, i ≤ j → m j ∣ m i := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [m] <;>
      first
        | exact dvd_refl _
        | exact hd21
        | exact hd32
        | exact dvd_trans hd32 hd21
  have hbig : ∀ k : Fin 3, 2 * T < (m k : ℝ) * Work.HP.lam L (k.val + 1) := by
    intro k
    fin_cases k
    · show 2 * T < (m1 : ℝ) * Work.HP.lam L 1
      have h3 : T / Work.HP.lam L 1 < (m1 : ℝ) / 2 := by linarith
      have h4 := (div_lt_iff₀ hL1).mp h3
      linarith
    · show 2 * T < (m2 : ℝ) * Work.HP.lam L 2
      have h3 : T / Work.HP.lam L 2 < (m2 : ℝ) / 2 := by linarith
      have h4 := (div_lt_iff₀ hL2).mp h3
      linarith
    · show 2 * T < (m3 : ℝ) * Work.HP.lam L 3
      have h3 : T / Work.HP.lam L 3 < (m3 : ℝ) / 2 := by linarith
      have h4 := (div_lt_iff₀ hL3).mp h3
      linarith
  -- the sublattice
  set Λt : Submodule ℤ (Fin 5 → ℤ) :=
    Submodule.span ℤ (Set.range fun i : Fin 3 => (m i : ℤ) • b i) with hΛt
  have hΛtL : Λt ≤ L := by
    rw [hΛt, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    rw [hbasis]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- the basis of `L` induced by `b`
  let bL : Fin 3 → L := fun i => ⟨b i, by rw [hbasis]; exact Submodule.subset_span ⟨i, rfl⟩⟩
  have hbLli : LinearIndependent ℤ bL := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc i
    refine hli c ?_ i
    have h := congrArg (Submodule.subtype L) hc
    simp only [map_sum, map_smul, Submodule.coe_subtype, map_zero] at h
    simpa [bL] using h
  have hbLspan : ⊤ ≤ Submodule.span ℤ (Set.range bL) := by
    intro x hx
    have hxL : (x : Fin 5 → ℤ) ∈ Submodule.span ℤ (Set.range b) := by
      rw [← hbasis]; exact x.2
    rw [Submodule.mem_span_range_iff_exists_fun] at hxL ⊢
    obtain ⟨c, hc⟩ := hxL
    refine ⟨c, ?_⟩
    apply Subtype.ext
    have h2 : (Submodule.subtype L (∑ i, c i • bL i)) = ∑ i, c i • b i := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
    change (Submodule.subtype L (∑ i, c i • bL i)) = (Submodule.subtype L x)
    rw [h2]
    exact hc
  let B : Module.Basis (Fin 3) ℤ L := Module.Basis.mk hbLli hbLspan
  have hB : ∀ i : Fin 3, ((B i : L) : Fin 5 → ℤ) = b i := fun i => by
    have h1 : (B i : L) = bL i := Module.Basis.mk_apply hbLli hbLspan i
    rw [h1]
  have hcoord : ∀ z : L, (z : Fin 5 → ℤ) = ∑ i, (B.repr z i) • b i := by
    intro z
    have h := congrArg (Submodule.subtype L) (B.sum_repr z)
    simp only [map_sum, map_smul, Submodule.coe_subtype] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [hB i]
  let κ := (i : Fin 3) → ZMod (m i)
  haveI : ∀ i : Fin 3, NeZero (m i) := fun i => ⟨(hmp i).ne'⟩
  let label : L → κ := fun x i => (B.repr x i : ZMod (m i))
  have hlabel : ∀ x y : L, label x = label y → ((x : Fin 5 → ℤ) - (y : Fin 5 → ℤ)) ∈ Λt := by
    intro x y hxy
    have hcoord' : ∀ i : Fin 3, (m i : ℤ) ∣ (B.repr x i - B.repr y i) := by
      intro i
      have h1 : (B.repr x i : ZMod (m i)) = (B.repr y i : ZMod (m i)) := congrFun hxy i
      have h4 : B.repr x i ≡ B.repr y i [ZMOD (m i : ℤ)] :=
        (ZMod.intCast_eq_intCast_iff (B.repr x i) (B.repr y i) (m i)).mp h1
      exact Int.ModEq.dvd h4.symm
    choose k hk using hcoord'
    have hsum : ((x : Fin 5 → ℤ) - (y : Fin 5 → ℤ))
        = ∑ i, k i • ((m i : ℤ) • b i) := by
      have h1 : (x : Fin 5 → ℤ) - (y : Fin 5 → ℤ)
          = ∑ i, ((B.repr x i - B.repr y i)) • b i := by
        rw [hcoord x, hcoord y, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
      rw [h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hk i, smul_smul]
      congr 1
      ring
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  set S : Set (Fin 5 → ℤ) := {v | Work.HP.eNorm v ≤ T} with hS
  have hSfin : S.Finite := Work.HP.MDBasic.finite_eNorm_le T
  have hkey := henkCoset L Λt hΛtL S hSfin label hlabel
  have hball : (Work.HP.ballCount L T : ℝ)
      = (({x : Fin 5 → ℤ | x ∈ L ∧ x ∈ S} : Set (Fin 5 → ℤ)).ncard : ℝ) := rfl
  rw [hball]
  have hcard : (({x : Fin 5 → ℤ | x ∈ L ∧ x ∈ S} : Set (Fin 5 → ℤ)).ncard : ℝ)
      ≤ (Fintype.card κ : ℝ) *
        (({x : Fin 5 → ℤ | x ∈ Λt ∧ ∃ y ∈ S, ∃ z ∈ S, y - z = x} : Set (Fin 5 → ℤ)).ncard : ℝ) := by
    exact_mod_cast hkey
  have hinner : ({x : Fin 5 → ℤ | x ∈ Λt ∧ ∃ y ∈ S, ∃ z ∈ S, y - z = x} : Set (Fin 5 → ℤ))
      = {0} := by
    ext x
    constructor
    · rintro ⟨hxA, y, hy, z, hz, rfl⟩
      have hyS : Work.HP.eNorm y ≤ T := hy
      have hzS : Work.HP.eNorm z ≤ T := hz
      have hsub : Work.HP.eNorm (y - z) ≤ 2 * T := by
        have h1 := Work.HP.MDEstimates.eNorm_sub_le y z
        linarith
      exact kill_At L hL T hT b hli hbasis hflag2 hflag3 m hmp hdvd hbig hxA hsub
    · rintro rfl
      have h0S : (0 : Fin 5 → ℤ) ∈ S := by
        rw [hS]
        simp only [Set.mem_setOf_eq]
        have hzero : Work.HP.eNorm (0 : Fin 5 → ℤ) = 0 := by simp [Work.HP.eNorm]
        rw [hzero]
        exact hT
      exact ⟨Submodule.zero_mem _, 0, h0S, 0, h0S, by simp⟩
  rw [hinner, Set.ncard_singleton, Nat.cast_one, mul_one] at hcard
  have hcardκ : (Fintype.card κ : ℝ) = ((∏ i : Fin 3, m i : ℕ) : ℝ) := by
    rw [Fintype.card_pi]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.card]
  rw [hcardκ] at hcard
  have hprod' : ((∏ i : Fin 3, m i : ℕ) : ℝ) = (m1 : ℝ) * (m2 : ℝ) * (m3 : ℝ) := by
    simp [m, Fin.prod_univ_three]
  rw [hprod'] at hcard
  have hrhs : (∏ j : Fin 3, (1 + T / Work.HP.lam L (j.val + 1)))
      = (1 + T / Work.HP.lam L 1) * (1 + T / Work.HP.lam L 2)
        * (1 + T / Work.HP.lam L 3) := by
    simp [Fin.prod_univ_three]
  rw [hrhs]
  linarith [hcard, hprod]


theorem ballCount_le (L : Submodule ℤ (Fin 5 → ℤ)) (hL : Work.HP.rk L = 3) (T : ℝ) (hT : 0 ≤ T) :
    (Work.HP.ballCount L T : ℝ) ≤ 27 * ∏ j : Fin 3, (1 + T / Work.HP.lam L (j.val + 1)) := by
  obtain ⟨b, hli, hbasis, hflag2, hflag3⟩ := exists_flagBasis L hL
  exact ballCount_le_of_basis L hL T hT b hli hbasis hflag2 hflag3

end Work.HP.Q44Child
