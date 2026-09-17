import Submission.E8NullVector
import Submission.Commons.Algebra.Lie.UeaNilpotent.smul_eq_zero_of_ad_local
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_weightSpace_reflect_finrank

/-!
# Local nilpotence of the lowering operators on the irreducible quotient

`Submission.E8NullVector` shows that `fᵢ^(λᵢ+1)` annihilates the highest weight vector of the
quotient `L = V ⧸ N` by the maximal submodule.  Here we upgrade this to **local nilpotence of
`fᵢ` on all of `L`**, using the local nilpotence of `ad (SerreF i)` on `U(e₈)`
(`Commons.Algebra.Lie.UeaNilpotent.smul_eq_zero_of_ad_local`, fed by
`Commons.Algebra.Lie.SerreConstruction.hloc_F`).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8LocallyNilpotent

open Submission.StarModule (wordElt Lop FA wordElt_nil Eword Lop_wordElt wrho Eop_apply)
open Submission.StarQuotient (Ebar Lbar Hbar J V Ebar_mk)
open Submission.VermaWeight
open Submission.E8NullVector
open Submission.E8Integrable (kI Ebar_v)

abbrev E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

abbrev L8 : Type := LieAlgebra.e₈ ℂ

/-- Powers of `LieModule.toEnd` agree with powers of the corresponding enveloping-algebra
element. -/
lemma toEnd_pow_eq {M : Type*} [AddCommGroup M] [Module ℂ M] [LieRingModule L8 M]
    [LieModule ℂ L8 M] [Module U M]
    (hι : ∀ (x : L8) (m : M), (UniversalEnvelopingAlgebra.ι ℂ x) • m = ⁅x, m⁆)
    (x : L8) (m : M) (k : ℕ) :
    ((LieModule.toEnd ℂ L8 M x)^k) m = ((UniversalEnvelopingAlgebra.ι ℂ x)^k) • m := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply]
      rw [show (LieModule.toEnd ℂ L8 M x) m = (UniversalEnvelopingAlgebra.ι ℂ x) • m
        from (hι x m).symm]
      rw [ih, ← mul_smul, pow_succ]

/-- The `U(e₈)`-module structure on the quotient by a submodule is compatible with the Lie
action. -/
lemma quot_hι (N : Submodule U V) (x : L8) (m : V ⧸ N) :
    (UniversalEnvelopingAlgebra.ι ℂ x) • m = ⁅x, m⁆ := by
  induction m using Submodule.Quotient.induction_on with
  | _ z =>
      rw [show (UniversalEnvelopingAlgebra.ι ℂ x) • (Submodule.Quotient.mk (p := N) z)
          = Submodule.Quotient.mk ((UniversalEnvelopingAlgebra.ι ℂ x) • z) from rfl]
      rw [show (UniversalEnvelopingAlgebra.ι ℂ x) • z = ⁅x, z⁆ from rfl]
      rfl

/-- **`fᵢ` is locally nilpotent on the quotient `V ⧸ N`.** -/
theorem f_locallyNilpotent (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (i : Fin 8) (y : V ⧸ N) :
    ∃ n : ℕ, (Submission.E8Weights.f i ^ n) • y = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective N y
  obtain ⟨u, hu⟩ := Submission.VermaNonzero.cyclic_V lam z
  have hy : N.mkQ z = u • N.mkQ v := by
    rw [← hu]
    rfl
  rw [hy]
  have hm : ∃ Nn : ℕ,
      ((LieModule.toEnd ℂ L8 (V ⧸ N) (Submission.E8Weights.SerreF i))^Nn) (N.mkQ v) = 0 := by
    refine ⟨kI i + 1, ?_⟩
    rw [toEnd_pow_eq (quot_hι N) (Submission.E8Weights.SerreF i)]
    exact f_pow_smul_vbar N hvN hmax i
  obtain ⟨n, hn⟩ := Commons.Algebra.Lie.UeaNilpotent.smul_eq_zero_of_ad_local
    (quot_hι N) (Submission.E8Weights.SerreF i)
    (Commons.Algebra.Lie.SerreConstruction.hloc_F i) hm u
  refine ⟨n, ?_⟩
  rw [toEnd_pow_eq (quot_hι N) (Submission.E8Weights.SerreF i)] at hn
  exact hn

/-! ## Local nilpotence of the raising operators

`Ebar i` acts on the word basis by deleting one letter `i`, so it strictly shortens words.  Hence
`eᵢ` is locally nilpotent on `L = V ⧸ N`. -/

/-- The span of the word vectors of length at most `K`. -/
def elen (K : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {x : V | ∃ w : List (Fin 8), w.length ≤ K ∧
    x = (Submodule.Quotient.mk (wordElt w) : V)}

lemma elen_mono {K K' : ℕ} (h : K ≤ K') : elen K ≤ elen K' := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨w, hw, rfl⟩
  exact Submodule.subset_span ⟨w, le_trans hw h, rfl⟩

lemma mk_mem_elen (w : List (Fin 8)) :
    (Submodule.Quotient.mk (wordElt w) : V) ∈ elen w.length :=
  Submodule.subset_span ⟨w, le_rfl, rfl⟩

/-- `Eword` shortens words. -/
lemma Eword_mem_short (i : Fin 8) (w : List (Fin 8)) :
    Submission.StarModule.Eword E8 lam i w ∈
      Submodule.span ℂ {y : FA (Fin 8) | ∃ w' : List (Fin 8),
        w'.length < w.length ∧ y = wordElt w'} := by
  induction w with
  | nil => simp [Submission.StarModule.Eword]
  | cons a v ih =>
      rw [show Submission.StarModule.Eword E8 lam i (a :: v)
          = Submission.StarModule.Lop a (Submission.StarModule.Eword E8 lam i v)
            + (if a = i then (lam i - Submission.StarModule.wrho E8 i v) • wordElt v else 0)
          from rfl]
      refine Submodule.add_mem _ ?_ ?_
      · refine Submodule.span_induction (p := fun y _ => Submission.StarModule.Lop a y ∈
          Submodule.span ℂ {y : FA (Fin 8) | ∃ w' : List (Fin 8),
            w'.length < (a :: v).length ∧ y = wordElt w'}) ?_ ?_ ?_ ?_ ih
        · rintro y ⟨w', hw', rfl⟩
          refine Submodule.subset_span ⟨a :: w', by simp; omega, ?_⟩
          rw [Submission.StarModule.Lop_wordElt]
        · simp
        · intro y z _ _ hy hz; rw [map_add]; exact Submodule.add_mem _ hy hz
        · intro c y _ hy; rw [map_smul]; exact Submodule.smul_mem _ _ hy
      · by_cases h : a = i
        · rw [if_pos h]
          refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, ?_, rfl⟩)
          simp
        · rw [if_neg h]; exact Submodule.zero_mem _

lemma Ebar_mem_elen (i : Fin 8) (K : ℕ) {x : V} (hx : x ∈ elen (K + 1)) :
    Ebar E8 lam i x ∈ elen K := by
  refine Submodule.span_induction (p := fun x _ => Ebar E8 lam i x ∈ elen K) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨w, hw, rfl⟩
    rw [Ebar_mk, Eop_apply]
    refine Submodule.span_induction (p := fun y _ =>
      (Submodule.Quotient.mk y : V) ∈ elen K) ?_ ?_ ?_ ?_ (Eword_mem_short i w)
    · rintro y ⟨w', hw', rfl⟩
      exact Submodule.subset_span ⟨w', by omega, rfl⟩
    · simp
    · intro y z _ _ hy hz; rw [Submodule.Quotient.mk_add]; exact Submodule.add_mem _ hy hz
    · intro c y _ hy; rw [Submodule.Quotient.mk_smul]; exact Submodule.smul_mem _ _ hy
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx

lemma Ebar_mem_elen_zero (i : Fin 8) {x : V} (hx : x ∈ elen 0) : Ebar E8 lam i x = 0 := by
  refine Submodule.span_induction (p := fun x _ => Ebar E8 lam i x = 0) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨w, hw, rfl⟩
    have hw0 : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hw)
    subst hw0
    rw [wordElt_nil]
    exact Ebar_v i
  · simp
  · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
  · intro c x _ hx; rw [map_smul, hx, smul_zero]

lemma Ebar_pow_mem_elen (i : Fin 8) (K N : ℕ) {x : V} (hx : x ∈ elen (K + N)) :
    ((Ebar E8 lam i)^N) x ∈ elen K := by
  induction N generalizing x with
  | zero => simpa using hx
  | succ N ih =>
      rw [pow_succ, Module.End.mul_apply]
      rw [Nat.add_succ] at hx
      exact ih (Ebar_mem_elen i (K + N) hx)

lemma e_pow_smul_eq (i : Fin 8) (c : ℕ) (y : V) :
    (Submission.E8Weights.e i ^ c) • y = ((Ebar E8 lam i)^c) y := by
  induction c generalizing y with
  | zero => simp
  | succ c ih =>
      rw [pow_succ, mul_smul, ih, e_smul_eq, pow_succ, Module.End.mul_apply]

/-- **`eᵢ` is locally nilpotent on the quotient `V ⧸ N`.** -/
theorem e_locallyNilpotent (N : Submodule U V) (i : Fin 8) (y : V ⧸ N) :
    ∃ n : ℕ, (Submission.E8Weights.e i ^ n) • y = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective N y
  have hz : z ∈ Submodule.span ℂ (Set.range (fun w : List (Fin 8) =>
      (Submodule.Quotient.mk (wordElt w) : V))) := by
    rw [span_mk_wordElt_eq_top]; trivial
  obtain ⟨s, hs⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  -- `s` is a finitely supported function on words
  set K : ℕ := s.support.sup (fun w => w.length) with hK
  have hzK : z ∈ elen K := by
    rw [← hs]
    refine Submodule.sum_mem _ fun w hw => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨w, Finset.le_sup (f := fun w : List (Fin 8) => w.length) hw, rfl⟩)
  refine ⟨K + 2, ?_⟩
  change Submodule.Quotient.mk ((Submission.E8Weights.e i ^ (K + 2)) • z) = 0
  rw [e_pow_smul_eq]
  rw [show K + 2 = (K + 1) + 1 by omega, pow_succ', Module.End.mul_apply]
  have h0 : ((Ebar E8 lam i ^ (K + 1)) z) ∈ elen 0 :=
    Ebar_pow_mem_elen i 0 (K + 1) (elen_mono (by omega) hzK)
  rw [show ((Ebar E8 lam i) ((Ebar E8 lam i ^ (K + 1)) z)) = 0 from Ebar_mem_elen_zero i h0]
  exact Submodule.Quotient.mk_zero (p := N)

end Submission.E8LocallyNilpotent
