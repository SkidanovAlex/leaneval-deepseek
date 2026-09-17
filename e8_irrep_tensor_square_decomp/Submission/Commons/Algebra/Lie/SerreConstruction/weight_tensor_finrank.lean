import Mathlib
import Submission.Commons.Algebra.Lie.SerreConstruction.weight_mult_wact
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_isKilling
import Submission.Commons.Algebra.Lie.SerreConstruction.eq_top_of_lieSubalgebra_of_generators
import Submission.Commons.Algebra.Lie.CompleteReducibility.isCompl_of_isKilling
import Submission.Commons.LinearAlgebra.End.exists_joint_eigenvector
import Submission.Commons.LinearAlgebra.End.sl2_span_finite_stable
import Submission.Commons.Algebra.Lie.Sl2.string_of_locallyNilpotent

/-!
# Weight spaces of a tensor product of `e₈`-modules

For finite-dimensional modules `M`, `N` over the Serre-constructed `e₈` (`L8`) and any weight `ν`,
the `ν`-weight space of the tensor product is the direct sum of the tensor products of the weight
spaces:

  `(M ⊗ N)_ν = ⊕_{ξ} M_ξ ⊗ N_{ν - ξ}`,

and hence, for any finite set `s` containing all the weights of `M`,

  `dim (M ⊗ N)_ν = ∑_{ξ ∈ s} dim M_ξ · dim N_{ν - ξ}`.

The ingredients are:

* `eigenvalue_int`: every eigenvalue of `Hᵢ` on a finite-dimensional `e₈`-module is an integer
  (the `𝔰𝔩₂`-string argument, using `Commons.Algebra.Lie.Sl2.string_of_locallyNilpotent`);
* `Mwt_iSupIndep`: the weight spaces are independent, deduced from Mathlib's independence of the
  *simultaneous generalised* eigenspaces of a commuting family
  (`Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`);
* `Mwt_iSup_eq_top`: the weight spaces of a finite-dimensional `e₈`-module span it (Weyl's
  complete reducibility `Commons.Algebra.Lie.CompleteReducibility.isCompl_of_isKilling` + the
  existence of a common eigenvector of the commuting `Hᵢ`
  `Commons.LinearAlgebra.End.exists_joint_eigenvector` + the integrality above);
* `Mwt_tmul_mem`: a pure tensor of weight vectors is a weight vector of the tensor product
  (`TensorProduct.LieModule.lie_tmul_right`);
* the finrank computation for `map₂ (TensorProduct.mk ℂ M N) A B`.
-/

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct BigOperators
open Module

namespace Commons.Algebra.Lie.SerreConstruction

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [LieRingModule L8 M] [LieModule ℂ L8 M]
variable {N : Type*} [AddCommGroup N] [Module ℂ N] [LieRingModule L8 N] [LieModule ℂ L8 N]

/-! ## The `𝔰𝔩₂`-triples in `e₈` and integrality of the weights -/

lemma serre_isSl2Triple (i : Fin 8) : IsSl2Triple (SerreH i) (SerreE i) (SerreF i) where
  h_ne_zero := e8_H_linearIndependent.ne_zero i
  lie_e_f := by rw [serreLie_E_F, if_pos rfl]
  lie_h_e_nsmul := by
    rw [serreLie_H_E, show E8 i i = 2 from E8_diag i, zsmul_int_eq]
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ) 2 (SerreE i)]
    norm_num
  lie_h_f_nsmul := by
    rw [serreLie_H_F, show E8 i i = 2 from E8_diag i]
    rw [show -((2 : ℤ)) = (-(2 : ℤ)) from rfl, zsmul_int_eq]
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ) 2 (SerreF i)]
    norm_num

/-- **Every eigenvalue of `Hᵢ` on a finite-dimensional `e₈`-module is an integer.**

Raise an eigenvector to the "top" of its `Eᵢ`-string, so that it is primitive (killed by `Eᵢ`);
the classical `𝔰𝔩₂`-string computation then shows that the eigenvalue of `Hᵢ` on a primitive
vector is `N - 1` with `N ∈ ℕ` the length of its `Fᵢ`-string. -/
theorem eigenvalue_int {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L8 V]
    [LieModule ℂ L8 V] [Module.Finite ℂ V] (i : Fin 8) (v : V) (hv : v ≠ 0) (lam : ℂ)
    (hlam : LieModule.toEnd ℂ L8 V (SerreH i) v = lam • v) : ∃ n : ℤ, lam = (n : ℂ) := by
  classical
  set E := LieModule.toEnd ℂ L8 V (SerreE i) with hE
  obtain ⟨N, hN⟩ := localNilpotent_e (M := V) i v
  have hex : ∃ n, (E ^ n) v = 0 := ⟨N, hN⟩
  have hn₀ : (E ^ Nat.find hex) v = 0 := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h] at hn₀; simp only [pow_zero, Module.End.one_apply] at hn₀; exact absurd hn₀ hv
    · exact h
  set k := Nat.find hex - 1 with hk
  have hk1 : k + 1 = Nat.find hex := Nat.succ_pred_eq_of_pos hpos
  have hw0 : (E ^ k) v ≠ 0 := by
    intro h
    exact Nat.find_min hex (by omega : k < Nat.find hex) h
  have hEw : E ((E ^ k) v) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ', hk1, hn₀]
  have hHw : LieModule.toEnd ℂ L8 V (SerreH i) ((E ^ k) v)
      = (lam + (2 * k : ℕ)) • ((E ^ k) v) := by
    have h1 := Commons.LinearAlgebra.End.sl2_h_apply_pow_e
      (LieModule.toEnd ℂ L8 V (SerreH i)) (LieModule.toEnd ℂ L8 V (SerreE i))
      (H_mul_E_sub (M := V) i) k v
    rw [hlam, map_smul] at h1
    rw [h1, ← add_smul]
  obtain ⟨N', hN'pos, hN'eq, -, -⟩ := Commons.Algebra.Lie.Sl2.string_of_locallyNilpotent
    (serre_isSl2Triple i) (fun m => localNilpotent_e (M := V) i m)
    (fun m => localNilpotent_f (M := V) i m) ((E ^ k) v) hw0
    (show ⁅SerreE i, (E ^ k) v⁆ = 0 from hEw) (lam + (2 * k : ℕ))
    (show ⁅SerreH i, (E ^ k) v⁆ = (lam + (2 * k : ℕ)) • (E ^ k) v from hHw)
  refine ⟨(N' : ℤ) - 2 * k - 1, ?_⟩
  have hkk : lam = (N' : ℂ) - 2 * k - 1 := by
    rw [hN'eq]
    push_cast
    ring
  rw [hkk]
  push_cast
  ring

/-! ## Independence of the weight spaces -/

/-- The simultaneous **generalised** weight spaces of any module over `L8`, relative to the
commuting operators `Hᵢ`, are independent. -/
lemma genWeight_iSupIndep {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L8 V]
    [LieModule ℂ L8 V] :
    iSupIndep (fun χ : Fin 8 → ℂ =>
      ⨅ j : Fin 8, (LieModule.toEnd ℂ L8 V (SerreH j)).maxGenEigenspace (χ j)) := by
  refine Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (f := fun j : Fin 8 => LieModule.toEnd ℂ L8 V (SerreH j)) ?_
  intro i j φ
  exact Module.End.mapsTo_maxGenEigenspace_of_comm
    (show LieModule.toEnd ℂ L8 V (SerreH j) * LieModule.toEnd ℂ L8 V (SerreH i)
        = LieModule.toEnd ℂ L8 V (SerreH i) * LieModule.toEnd ℂ L8 V (SerreH j) from
      (sub_eq_zero.mp (by rw [toEnd_mul_sub, serreLie_HH, map_zero])).symm) φ

lemma intWeight_injective :
    Function.Injective (fun ξ : Fin 8 → ℤ => fun j : Fin 8 => ((ξ j : ℤ) : ℂ)) := by
  intro a b h
  funext j
  exact Int.cast_injective (congrFun h j)

lemma Mwt_le_genWeight {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L8 V]
    [LieModule ℂ L8 V] (ξ : Fin 8 → ℤ) :
    Mwt (M := V) ξ ≤ ⨅ j : Fin 8,
      (LieModule.toEnd ℂ L8 V (SerreH j)).maxGenEigenspace (((ξ j : ℤ)) : ℂ) := by
  rw [Mwt]
  exact iInf_mono fun j => Module.End.eigenspace_le_maxGenEigenspace

/-- **The weight spaces of any module over `L8` are independent.** -/
lemma Mwt_iSupIndep {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L8 V]
    [LieModule ℂ L8 V] : iSupIndep (fun ξ : Fin 8 → ℤ => Mwt (M := V) ξ) :=
  ((genWeight_iSupIndep (V := V)).comp intWeight_injective).mono
    (fun ξ => Mwt_le_genWeight ξ)

/-- The same, shifted: the shifted weight spaces `Mwt (ξ + ·)` are independent. -/
lemma Mwt_iSupIndep_shift {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L8 V]
    [LieModule ℂ L8 V] (ξ : Fin 8 → ℤ) :
    iSupIndep (fun η : Fin 8 → ℤ => Mwt (M := V) (ξ + η)) :=
  (Mwt_iSupIndep (V := V)).comp (fun a b h => add_left_cancel h)

/-- A vector of `Mwt ν` is disjoint from the span of the weight spaces of weights different
from `ν`. -/
lemma Mwt_disjoint {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L8 V]
    [LieModule ℂ L8 V] (F : Finset (Fin 8 → ℤ)) {ν : Fin 8 → ℤ} (h : ν ∉ F) :
    Mwt (M := V) ν ⊓ (⨆ γ ∈ F, Mwt (M := V) γ) = ⊥ :=
  ((Mwt_iSupIndep (V := V)).disjoint_biSup (x := ν) (y := ↑F) (by simpa using h)).eq_bot

/-- A sum of weight components of weights different from `ν` lying in `Mwt ν` vanishes. -/
lemma sum_eq_zero_of_mem_Mwt_ne {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L8 V]
    [LieModule ℂ L8 V] {ι : Type*} (F : Finset ι) (γ : ι → Fin 8 → ℤ) (v : ι → V)
    (hv : ∀ ξ ∈ F, v ξ ∈ Mwt (M := V) (γ ξ)) {ν : Fin 8 → ℤ} (hνF : ∀ ξ ∈ F, γ ξ ≠ ν)
    (hν : ∑ ξ ∈ F, v ξ ∈ Mwt (M := V) ν) : ∑ ξ ∈ F, v ξ = 0 := by
  have hνimage : ν ∉ F.image γ := by
    intro h
    obtain ⟨ξ, hξ, hγ⟩ := Finset.mem_image.mp h
    exact hνF ξ hξ hγ
  have hmem : ∑ ξ ∈ F, v ξ ∈ Mwt (M := V) ν ⊓ (⨆ γ' ∈ F.image γ, Mwt (M := V) γ') :=
    ⟨hν, Submodule.sum_mem _ fun ξ hξ =>
      Submodule.mem_iSup_of_mem (γ ξ) (Submodule.mem_iSup_of_mem
        (Finset.mem_image_of_mem γ hξ) (hv ξ hξ))⟩
  rw [Mwt_disjoint (F.image γ) hνimage] at hmem
  exact hmem

/-- **Linear independence of weight components.** -/
lemma decomp_unique {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L8 V]
    [LieModule ℂ L8 V] (F : Finset (Fin 8 → ℤ)) (v : (Fin 8 → ℤ) → V)
    (hv : ∀ ξ ∈ F, v ξ ∈ Mwt (M := V) ξ) (hsum : ∑ ξ ∈ F, v ξ = 0) :
    ∀ ξ ∈ F, v ξ = 0 :=
  (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (fun ξ => Mwt (M := V) ξ)).mp
    (Mwt_iSupIndep) F v hv hsum

/-- **Component extraction.**  If `x = ∑_{p ∈ G} z p` where `z p` lies in the weight space of
`γ p` and `x` itself is a weight vector of weight `ν`, then only the components with `γ p = ν`
contribute. -/
lemma sum_filter_eq_of_mem_Mwt {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L8 V]
    [LieModule ℂ L8 V] {ι : Type*} (G : Finset ι) (γ : ι → Fin 8 → ℤ) (z : ι → V)
    (hz : ∀ p ∈ G, z p ∈ Mwt (M := V) (γ p)) {ν : Fin 8 → ℤ}
    (hx : ∑ p ∈ G, z p ∈ Mwt (M := V) ν) :
    ∑ p ∈ G, z p = ∑ p ∈ G.filter (fun p => γ p = ν), z p := by
  classical
  set G' := G.filter (fun p => γ p ≠ ν) with hG'
  have hsplit : ∑ p ∈ G, z p
      = (∑ p ∈ G.filter (fun p => γ p = ν), z p) + ∑ p ∈ G', z p := by
    rw [hG', ← Finset.sum_filter_add_sum_filter_not G (fun p => γ p = ν) z]
  have hmem : ∑ p ∈ G', z p ∈ Mwt (M := V) ν := by
    have h1 : (∑ p ∈ G, z p) - (∑ p ∈ G.filter (fun p => γ p = ν), z p)
        ∈ Mwt (M := V) ν :=
      Submodule.sub_mem _ hx (Submodule.sum_mem _ fun p hp => by
        rw [Finset.mem_filter] at hp
        rw [← hp.2]
        exact hz p hp.1)
    rwa [hsplit, add_sub_cancel_left] at h1
  have hzero : ∑ p ∈ G', z p = 0 := by
    refine sum_eq_zero_of_mem_Mwt_ne G' γ z (fun p hp => ?_) (fun p hp hc => ?_) hmem
    · rw [hG', Finset.mem_filter] at hp
      exact hz p hp.1
    · rw [hG', Finset.mem_filter] at hp
      exact hp.2 hc
  rw [hsplit, hzero, add_zero]

/-! ## The weight spaces span a finite-dimensional module -/

lemma toEnd_h_mem_iSup_Mwt {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L8 V]
    [LieModule ℂ L8 V] (i : Fin 8) {v : V} (hv : v ∈ ⨆ ξ, Mwt (M := V) ξ) :
    LieModule.toEnd ℂ L8 V (SerreH i) v ∈ ⨆ ξ, Mwt (M := V) ξ := by
  refine Submodule.iSup_induction (p := fun ξ => Mwt (M := V) ξ)
    (motive := fun v => LieModule.toEnd ℂ L8 V (SerreH i) v ∈ ⨆ ξ, Mwt (M := V) ξ)
    hv ?_ ?_ ?_
  · intro ξ x hx
    exact Submodule.mem_iSup_of_mem ξ (toEnd_h_mem_Mwt i hx)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb

lemma toEnd_e_mem_iSup_Mwt {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L8 V]
    [LieModule ℂ L8 V] (i : Fin 8) {v : V} (hv : v ∈ ⨆ ξ, Mwt (M := V) ξ) :
    LieModule.toEnd ℂ L8 V (SerreE i) v ∈ ⨆ ξ, Mwt (M := V) ξ := by
  refine Submodule.iSup_induction (p := fun ξ => Mwt (M := V) ξ)
    (motive := fun v => LieModule.toEnd ℂ L8 V (SerreE i) v ∈ ⨆ ξ, Mwt (M := V) ξ)
    hv ?_ ?_ ?_
  · intro ξ x hx
    exact Submodule.mem_iSup_of_mem (fun j => ξ j + E8 j i) (toEnd_e_mem_Mwt i hx)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb

lemma toEnd_f_mem_iSup_Mwt {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L8 V]
    [LieModule ℂ L8 V] (i : Fin 8) {v : V} (hv : v ∈ ⨆ ξ, Mwt (M := V) ξ) :
    LieModule.toEnd ℂ L8 V (SerreF i) v ∈ ⨆ ξ, Mwt (M := V) ξ := by
  refine Submodule.iSup_induction (p := fun ξ => Mwt (M := V) ξ)
    (motive := fun v => LieModule.toEnd ℂ L8 V (SerreF i) v ∈ ⨆ ξ, Mwt (M := V) ξ)
    hv ?_ ?_ ?_
  · intro ξ x hx
    exact Submodule.mem_iSup_of_mem (fun j => ξ j - E8 j i) (toEnd_f_mem_Mwt i hx)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb

/-- **The weight spaces of a finite-dimensional `e₈`-module span it.** -/
theorem Mwt_iSup_eq_top {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L8 V]
    [LieModule ℂ L8 V] [Module.Finite ℂ V] : (⨆ ξ : Fin 8 → ℤ, Mwt (M := V) ξ) = ⊤ := by
  classical
  set W : Submodule ℂ V := ⨆ ξ : Fin 8 → ℤ, Mwt (M := V) ξ with hW
  have hWmem : ∀ ξ : Fin 8 → ℤ, Mwt (M := V) ξ ≤ W := fun ξ => le_iSup _ ξ
  have hV : ∀ x : L8, ∀ v ∈ W, ⁅x, v⁆ ∈ W := by
    let A : LieSubalgebra ℂ L8 :=
      { carrier := {x | ∀ v ∈ W, ⁅x, v⁆ ∈ W}
        zero_mem' := by intro v _; rw [zero_lie]; exact W.zero_mem
        add_mem' := by intro a b ha hb v hv; rw [add_lie]; exact W.add_mem (ha v hv) (hb v hv)
        smul_mem' := by intro c x hx v hv; rw [smul_lie]; exact W.smul_mem c (hx v hv)
        lie_mem' := by
          intro x y hx hy v hv
          have h1 : ⁅x, ⁅y, v⁆⁆ ∈ W := hx (⁅y, v⁆) (hy v hv)
          have h2 : ⁅y, ⁅x, v⁆⁆ ∈ W := hy (⁅x, v⁆) (hx v hv)
          have h3 : ⁅⁅x, y⁆, v⁆ = ⁅x, ⁅y, v⁆⁆ - ⁅y, ⁅x, v⁆⁆ := by rw [leibniz_lie]; abel
          rw [h3]
          exact W.sub_mem h1 h2 }
    have hgen : ∀ g : CartanMatrix.Generators (Fin 8),
        LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ g) ∈ A := by
      intro g
      cases g with
      | H i => intro v hv; exact toEnd_h_mem_iSup_Mwt i hv
      | E i => intro v hv; exact toEnd_e_mem_iSup_Mwt i hv
      | F i => intro v hv; exact toEnd_f_mem_iSup_Mwt i hv
    have htop : A = ⊤ := eq_top_of_lieSubalgebra_of_generators CartanMatrix.E₈ A hgen
    intro x v hv
    exact (show x ∈ A from by rw [htop]; trivial) v hv
  let W' : LieSubmodule ℂ L8 V :=
    { W with lie_mem := fun {x} {m} hm => hV x m hm }
  have hkill : LieAlgebra.IsKilling ℂ L8 := e8_isKilling
  haveI := hkill
  obtain ⟨W₂, hW₂⟩ := Commons.Algebra.Lie.CompleteReducibility.isCompl_of_isKilling W'
  have hbot : W₂ = ⊥ := by
    by_contra hne
    have hne' : (W₂ : Submodule ℂ V) ≠ ⊥ := fun h =>
      hne ((LieSubmodule.toSubmodule_inj W₂ ⊥).mp (by simpa using h))
    obtain ⟨w, lam, hwW, hw0, hl⟩ := Commons.LinearAlgebra.End.exists_joint_eigenvector
      (fun j : Fin 8 => LieModule.toEnd ℂ L8 V (SerreH j))
      (fun i j => show LieModule.toEnd ℂ L8 V (SerreH i) * LieModule.toEnd ℂ L8 V (SerreH j)
          = LieModule.toEnd ℂ L8 V (SerreH j) * LieModule.toEnd ℂ L8 V (SerreH i) from
        sub_eq_zero.mp (by rw [toEnd_mul_sub, serreLie_HH, map_zero]))
      (W₂ : Submodule ℂ V) hne' (fun i x hx => W₂.lie_mem hx)
    have hξ : ∀ j : Fin 8, ∃ n : ℤ, lam j = (n : ℂ) :=
      fun j => eigenvalue_int j w hw0 (lam j) (hl j)
    let ξ : Fin 8 → ℤ := fun j => Classical.choose (hξ j)
    have hξspec : ∀ j : Fin 8, lam j = ((ξ j : ℤ) : ℂ) := fun j => Classical.choose_spec (hξ j)
    have hwMwt : w ∈ Mwt (M := V) ξ := by
      rw [mem_Mwt_iff]
      intro j
      rw [← hξspec j]
      exact hl j
    have hmem : w ∈ W' ⊓ W₂ := ⟨hWmem ξ hwMwt, hwW⟩
    rw [hW₂.1.eq_bot] at hmem
    exact hw0 (by simpa using hmem)
  have htopW : (W : Submodule ℂ V) = ⊤ := by
    have h : W' = ⊤ := by
      have h2 : W' ⊔ W₂ = ⊤ := codisjoint_iff.mp hW₂.2
      rw [hbot, sup_bot_eq] at h2
      exact h2
    have h3 := congrArg (fun K : LieSubmodule ℂ L8 V => (K : Submodule ℂ V)) h
    exact h3
  exact htopW

/-! ## Finrank of `map₂ (TensorProduct.mk ℂ M N) A B` -/

theorem finrank_map₂_mk {P Q : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q]
    [Module ℂ Q] (A : Submodule ℂ P) (B : Submodule ℂ Q) :
    Module.finrank ℂ ↥(Submodule.map₂ (TensorProduct.mk ℂ P Q) A B)
      = Module.finrank ℂ ↥A * Module.finrank ℂ ↥B := by
  classical
  obtain ⟨A', hA'⟩ := Submodule.exists_isCompl A
  obtain ⟨B', hB'⟩ := Submodule.exists_isCompl B
  let πA : P →ₗ[ℂ] ↥A :=
    (LinearMap.fst ℂ ↥A ↥A').comp (Submodule.prodEquivOfIsCompl A A' hA').symm.toLinearMap
  let πB : Q →ₗ[ℂ] ↥B :=
    (LinearMap.fst ℂ ↥B ↥B').comp (Submodule.prodEquivOfIsCompl B B' hB').symm.toLinearMap
  have hπA : ∀ a : ↥A, πA (a : P) = a := fun a =>
    congrArg Prod.fst (Submodule.prodEquivOfIsCompl_symm_apply_left A A' hA' a)
  have hπB : ∀ b : ↥B, πB (b : Q) = b := fun b =>
    congrArg Prod.fst (Submodule.prodEquivOfIsCompl_symm_apply_left B B' hB' b)
  have hid : ∀ x : ↥A ⊗[ℂ] ↥B,
      (TensorProduct.map πA πB) ((TensorProduct.mapIncl A B) x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [TensorProduct.mapIncl, hπA a, hπB b]
    | add x y hx hy => simp [map_add, hx, hy]
  have hinj : Function.Injective (TensorProduct.mapIncl A B) := by
    intro x y hxy
    have hx := hid x
    have hy := hid y
    rw [hxy] at hx
    exact hx.symm.trans hy
  rw [← TensorProduct.range_mapIncl A B, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_tensorProduct]

/-! ## The tensor product of the weight spaces -/

/-- The image of `A ⊗ B` in `M ⊗ N` under the canonical map. -/
def tensorSub (A : Submodule ℂ M) (B : Submodule ℂ N) : Submodule ℂ (M ⊗[ℂ] N) :=
  Submodule.map₂ (TensorProduct.mk ℂ M N) A B

lemma tmul_mem_tensorSub {A : Submodule ℂ M} {B : Submodule ℂ N} {m : M} {n : N}
    (hm : m ∈ A) (hn : n ∈ B) : (m ⊗ₜ[ℂ] n) ∈ tensorSub A B := by
  rw [tensorSub, Submodule.map₂_eq_span_image2]
  exact Submodule.subset_span ⟨m, hm, n, hn, rfl⟩

lemma tensorSub_bot_left (B : Submodule ℂ N) :
    tensorSub (⊥ : Submodule ℂ M) B = ⊥ := by
  rw [tensorSub]
  refine le_antisymm ?_ bot_le
  rw [Submodule.map₂_le]
  intro m hm n _
  rw [Submodule.mem_bot] at hm ⊢
  rw [hm]
  simp

/-- A pure tensor of weight vectors is a weight vector of the tensor product. -/
lemma Mwt_tmul_mem {ξ η : Fin 8 → ℤ} {m : M} {n : N}
    (hm : m ∈ Mwt (M := M) ξ) (hn : n ∈ Mwt (M := N) η) :
    (m ⊗ₜ[ℂ] n) ∈ Mwt (M := M ⊗[ℂ] N) (ξ + η) := by
  rw [mem_Mwt_iff] at hm hn ⊢
  intro j
  have hmj : ⁅SerreH j, m⁆ = (((ξ j : ℤ)) : ℂ) • m := hm j
  have hnj : ⁅SerreH j, n⁆ = (((η j : ℤ)) : ℂ) • n := hn j
  rw [show LieModule.toEnd ℂ L8 (M ⊗[ℂ] N) (SerreH j) (m ⊗ₜ[ℂ] n)
      = ⁅SerreH j, m ⊗ₜ[ℂ] n⁆ from rfl, TensorProduct.LieModule.lie_tmul_right, hmj, hnj]
  rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', ← add_smul]
  congr 1
  simp only [Pi.add_apply, Int.cast_add]

lemma tensorSub_le_Mwt {ξ η : Fin 8 → ℤ} :
    tensorSub (Mwt (M := M) ξ) (Mwt (M := N) η) ≤ Mwt (M := M ⊗[ℂ] N) (ξ + η) := by
  rw [tensorSub, Submodule.map₂_le]
  intro m hm n hn
  exact Mwt_tmul_mem hm hn

/-- Every pure tensor lies in the sum of the tensor products of the weight spaces. -/
lemma tmul_mem_iSup_tensorSub [Module.Finite ℂ M] [Module.Finite ℂ N] (m : M) (n : N) :
    (m ⊗ₜ[ℂ] n) ∈ ⨆ (ξ : Fin 8 → ℤ) (η : Fin 8 → ℤ),
      tensorSub (Mwt (M := M) ξ) (Mwt (M := N) η) := by
  classical
  have hm : m ∈ ⨆ ξ : Fin 8 → ℤ, Mwt (M := M) ξ := by
    rw [Mwt_iSup_eq_top]; trivial
  obtain ⟨Sm, hm⟩ := (Submodule.mem_iSup_iff_exists_finset
    (p := fun ξ => Mwt (M := M) ξ)).mp hm
  obtain ⟨fm, hsumm⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
    (fun ξ => Mwt (M := M) ξ) m).mp hm
  let F : (Fin 8 → ℤ) → M := fun ξ => (fm ξ : M)
  have hF : ∀ ξ, F ξ ∈ Mwt (M := M) ξ := fun ξ => (fm ξ).2
  have hn : n ∈ ⨆ η : Fin 8 → ℤ, Mwt (M := N) η := by
    rw [Mwt_iSup_eq_top]; trivial
  obtain ⟨Tn, hn⟩ := (Submodule.mem_iSup_iff_exists_finset
    (p := fun η => Mwt (M := N) η)).mp hn
  obtain ⟨gn, hsumn⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
    (fun η => Mwt (M := N) η) n).mp hn
  let G : (Fin 8 → ℤ) → N := fun η => (gn η : N)
  have hG : ∀ η, G η ∈ Mwt (M := N) η := fun η => (gn η).2
  rw [show m = ∑ ξ ∈ Sm, F ξ from hsumm.symm, show n = ∑ η ∈ Tn, G η from hsumn.symm]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum]
  refine Submodule.sum_mem _ fun a ha => Submodule.sum_mem _ fun b hb => ?_
  show (F b ⊗ₜ[ℂ] G a) ∈ ⨆ (ξ' : Fin 8 → ℤ) (η' : Fin 8 → ℤ),
    tensorSub (Mwt (M := M) ξ') (Mwt (M := N) η')
  refine Submodule.mem_iSup_of_mem b ?_
  show (F b ⊗ₜ[ℂ] G a) ∈ ⨆ (η' : Fin 8 → ℤ),
    tensorSub (Mwt (M := M) b) (Mwt (M := N) η')
  exact Submodule.mem_iSup_of_mem a (tmul_mem_tensorSub (hF b) (hG a))

/-- The sum of the tensor products of the weight spaces is the whole tensor product. -/
lemma iSup_tensorSub_eq_top [Module.Finite ℂ M] [Module.Finite ℂ N] :
    (⨆ (ξ : Fin 8 → ℤ) (η : Fin 8 → ℤ),
      tensorSub (Mwt (M := M) ξ) (Mwt (M := N) η)) = ⊤ := by
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top (R := ℂ) (M := M) (N := N)]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨m, n, rfl⟩
  exact tmul_mem_iSup_tensorSub m n

/-- The first-factor Cartan operators on a tensor product commute. -/
lemma rTensor_cartan_commute {M : Type*} [AddCommGroup M] [Module ℂ M] [LieRingModule L8 M]
    [LieModule ℂ L8 M] {N : Type*} [AddCommGroup N] [Module ℂ N] (i j : Fin 8) :
    Commute ((LieModule.toEnd ℂ L8 M (SerreH j)).rTensor N)
      ((LieModule.toEnd ℂ L8 M (SerreH i)).rTensor N) := by
  show (LieModule.toEnd ℂ L8 M (SerreH j)).rTensor N
      * (LieModule.toEnd ℂ L8 M (SerreH i)).rTensor N
    = (LieModule.toEnd ℂ L8 M (SerreH i)).rTensor N
      * (LieModule.toEnd ℂ L8 M (SerreH j)).rTensor N
  rw [← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul]
  congr 1
  exact (sub_eq_zero.mp (by rw [toEnd_mul_sub, serreLie_HH, map_zero])).symm

/-- The simultaneous generalised eigenspaces of the first-factor Cartan operators on `M ⊗ N`
are independent. -/
lemma rTensor_genWeight_iSupIndep {M : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule L8 M] [LieModule ℂ L8 M] {N : Type*} [AddCommGroup N] [Module ℂ N]
    [LieRingModule L8 N] [LieModule ℂ L8 N] :
    iSupIndep (fun χ : Fin 8 → ℂ => ⨅ j : Fin 8,
      Module.End.maxGenEigenspace ((LieModule.toEnd ℂ L8 M (SerreH j)).rTensor N) (χ j)) := by
  let f : Fin 8 → Module.End ℂ (M ⊗[ℂ] N) :=
    fun j => (LieModule.toEnd ℂ L8 M (SerreH j)).rTensor N
  have key : iSupIndep (fun χ : Fin 8 → ℂ => ⨅ j : Fin 8, (f j).maxGenEigenspace (χ j)) := by
    refine Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f ?_
    intro i j φ
    refine Module.End.mapsTo_maxGenEigenspace_of_comm ?_ φ
    exact rTensor_cartan_commute (M := M) (N := N) i j
  exact key

/-- A tensor product of weight spaces lies in a single simultaneous generalised eigenspace of the
first-factor Cartan operators. -/
lemma tensorSub_le_genWeight (ν ξ : Fin 8 → ℤ) :
    tensorSub (Mwt (M := M) ξ) (Mwt (M := N) (ν - ξ)) ≤
      ⨅ j : Fin 8, Module.End.maxGenEigenspace
        ((LieModule.toEnd ℂ L8 M (SerreH j)).rTensor N) (((ξ j : ℤ)) : ℂ) := by
  refine le_iInf fun j => ?_
  rw [tensorSub, Submodule.map₂_le]
  intro m hm n hn
  have hmm : LieModule.toEnd ℂ L8 M (SerreH j) m = (((ξ j : ℤ)) : ℂ) • m :=
    (mem_Mwt_iff.mp hm) j
  have hsplit : (((LieModule.toEnd ℂ L8 M (SerreH j)).rTensor N)
      - (((ξ j : ℤ)) : ℂ) • (1 : Module.End ℂ (M ⊗[ℂ] N))) (m ⊗ₜ[ℂ] n) = 0 := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.rTensor_tmul,
      hmm]
    rw [TensorProduct.smul_tmul', sub_self]
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨1, by rw [pow_one]; exact hsplit⟩

/-- **The tensor products of the weight spaces are independent.** -/
lemma tensorSub_iSupIndep (ν : Fin 8 → ℤ) :
    iSupIndep (fun ξ : Fin 8 → ℤ => tensorSub (Mwt (M := M) ξ) (Mwt (M := N) (ν - ξ))) :=
  ((rTensor_genWeight_iSupIndep (M := M) (N := N)).comp intWeight_injective).mono
    (fun ξ => tensorSub_le_genWeight ν ξ)

/-- Finrank summation over an independent finite family of subspaces. -/
lemma finrank_iSup_finset_of_disjoint {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] {ι : Type*} (s : Finset ι) (p : ι → Submodule ℂ V)
    (hind : ∀ (t : Finset ι), t ⊆ s → ∀ i ∈ s, i ∉ t → Disjoint (p i) (⨆ j ∈ t, p j)) :
    Module.finrank ℂ ↥(⨆ i ∈ s, p i) = ∑ i ∈ s, Module.finrank ℂ ↥(p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hsup : (⨆ i ∈ insert a s, p i) = p a ⊔ ⨆ i ∈ s, p i := by
        rw [← Finset.sup_eq_iSup, ← Finset.sup_eq_iSup, Finset.insert_eq, Finset.sup_union,
          Finset.sup_singleton]
      have hdisj : Disjoint (p a) (⨆ i ∈ s, p i) :=
        hind s (fun i hi => Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s) ha
      have hfin : Module.finrank ℂ ↥(p a ⊔ ⨆ i ∈ s, p i)
          = Module.finrank ℂ ↥(p a) + Module.finrank ℂ ↥(⨆ i ∈ s, p i) := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq (p a) (⨆ i ∈ s, p i)
        rw [hdisj.eq_bot, finrank_bot, add_zero] at h
        exact h
      have ih' := ih (fun t ht i hi hit =>
        hind t (fun j hj => Finset.mem_insert_of_mem (ht hj)) i (Finset.mem_insert_of_mem hi) hit)
      rw [Finset.sum_insert ha, hsup, hfin, ih']

/-! ## The main theorem -/

/-- **The weight space of a tensor product is the sum of the tensor products of the weight
spaces.** -/
theorem Mwt_tensor_eq_iSup [Module.Finite ℂ M] [Module.Finite ℂ N]
    (s : Finset (Fin 8 → ℤ)) (hs : ∀ ξ : Fin 8 → ℤ, Mwt (M := M) ξ ≠ ⊥ → ξ ∈ s)
    (ν : Fin 8 → ℤ) :
    Mwt (M := M ⊗[ℂ] N) ν
      = ⨆ ξ ∈ s, tensorSub (Mwt (M := M) ξ) (Mwt (M := N) (ν - ξ)) := by
  classical
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxsup : x ∈ ⨆ (p : (Fin 8 → ℤ) × (Fin 8 → ℤ)),
        tensorSub (Mwt (M := M) p.1) (Mwt (M := N) p.2) := by
      rw [iSup_prod, iSup_tensorSub_eq_top]
      trivial
    obtain ⟨G, hG⟩ := (Submodule.mem_iSup_iff_exists_finset
      (p := fun p : (Fin 8 → ℤ) × (Fin 8 → ℤ) =>
        tensorSub (Mwt (M := M) p.1) (Mwt (M := N) p.2))).mp hxsup
    obtain ⟨z, hsum⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
      (fun p : (Fin 8 → ℤ) × (Fin 8 → ℤ) =>
        tensorSub (Mwt (M := M) p.1) (Mwt (M := N) p.2)) x).mp hG
    let zz : (Fin 8 → ℤ) × (Fin 8 → ℤ) → M ⊗[ℂ] N := fun p => (z p : M ⊗[ℂ] N)
    have hzmem : ∀ p ∈ G, zz p ∈ Mwt (M := M ⊗[ℂ] N) (p.1 + p.2) :=
      fun p _ => tensorSub_le_Mwt (z p).2
    have hx' : ∑ p ∈ G, zz p ∈ Mwt (M := M ⊗[ℂ] N) ν := by
      rw [show ∑ p ∈ G, zz p = x from hsum]; exact hx
    rw [show x = ∑ p ∈ G, zz p from hsum.symm]
    rw [sum_filter_eq_of_mem_Mwt G (fun p => p.1 + p.2) zz hzmem hx']
    refine Submodule.sum_mem _ fun p hp => ?_
    rw [Finset.mem_filter] at hp
    obtain ⟨hpG, hpν⟩ := hp
    have h2 : p.2 = ν - p.1 := by rw [← hpν]; abel
    have hsub : tensorSub (Mwt (M := M) p.1) (Mwt (M := N) p.2)
        = tensorSub (Mwt (M := M) p.1) (Mwt (M := N) (ν - p.1)) := by rw [h2]
    have hzp : zz p ∈ tensorSub (Mwt (M := M) p.1) (Mwt (M := N) (ν - p.1)) := by
      rw [← hsub]
      exact (z p).2
    by_cases hξs : p.1 ∈ s
    · exact Submodule.mem_iSup_of_mem p.1 (Submodule.mem_iSup_of_mem hξs hzp)
    · have hbot : Mwt (M := M) p.1 = ⊥ := by
        by_contra h
        exact hξs (hs p.1 h)
      have hz0 : zz p = 0 := by
        rw [hbot, tensorSub_bot_left] at hzp
        simpa using hzp
      rw [hz0]
      exact Submodule.zero_mem _
  · refine iSup₂_le fun ξ hξ => ?_
    refine le_trans (tensorSub_le_Mwt (ξ := ξ) (η := ν - ξ)) ?_
    rw [add_sub_cancel]

theorem weight_tensor_finrank {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule Commons.Algebra.Lie.SerreConstruction.L8 M]
    [LieModule ℂ Commons.Algebra.Lie.SerreConstruction.L8 M] [Module.Finite ℂ M]
    [AddCommGroup N] [Module ℂ N]
    [LieRingModule Commons.Algebra.Lie.SerreConstruction.L8 N]
    [LieModule ℂ Commons.Algebra.Lie.SerreConstruction.L8 N] [Module.Finite ℂ N]
    (s : Finset (Fin 8 → ℤ))
    (hs : ∀ ξ : Fin 8 → ℤ, Commons.Algebra.Lie.SerreConstruction.Mwt (M := M) ξ ≠ ⊥ → ξ ∈ s)
    (ν : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(Commons.Algebra.Lie.SerreConstruction.Mwt
        (M := TensorProduct ℂ M N) ν)
      = ∑ ξ ∈ s, Module.finrank ℂ ↥(Commons.Algebra.Lie.SerreConstruction.Mwt (M := M) ξ)
          * Module.finrank ℂ
              ↥(Commons.Algebra.Lie.SerreConstruction.Mwt (M := N) (ν - ξ)) := by
  rw [Mwt_tensor_eq_iSup s hs ν]
  rw [finrank_iSup_finset_of_disjoint s
    (fun ξ => tensorSub (Mwt (M := M) ξ) (Mwt (M := N) (ν - ξ))) ?_]
  · refine Finset.sum_congr rfl fun ξ hξ => ?_
    rw [tensorSub, finrank_map₂_mk]
  · intro t ht i hi hit
    exact (tensorSub_iSupIndep (M := M) (N := N) ν).disjoint_biSup (x := i) (y := ↑t)
      (by simpa using hit)

end Commons.Algebra.Lie.SerreConstruction
