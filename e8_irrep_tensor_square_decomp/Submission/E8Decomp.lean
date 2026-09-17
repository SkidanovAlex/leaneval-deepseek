import Submission.E8TensorBound
import Submission.E8ConstChar

/-!
# The character decomposition of the tensor square

`T N = (V ⧸ N) ⊗[ℂ] (V ⧸ N)` is a finite-dimensional semisimple `U(e₈)`-module
(`Submission.E8TensorBound.isSemisimple_tensor`).  This file proves that the character of `T N` is the
sum of the characters (`Submission.E8ConstChar.chFun`) of its simple constituents, by strong
induction on the dimension: if `P ≠ 0` is a `U`-submodule, semisimplicity gives a simple `S ≤ P` and
a complement `Q ≤ P` with `S ⊔ Q = P`, `S ⊓ Q = ⊥`, and then the weight multiplicities add
(`TLwt_inf_sup` + `finrank_sup_add_finrank_inf_eq`).

⚠ The naive argument via the distributive law in the lattice of subspaces is **wrong** (that lattice
is modular but *not* distributive: `S ⊓ T = Q ⊓ T = ⊥` does **not** imply `(S ⊔ Q) ⊓ T = ⊥`).  The
correct argument uses the *module* structure: `TLwt ν` is the simultaneous eigenspace of the Cartan,
and `P = S ⊔ Q` is a decomposition of `U`-modules, so a Cartan-eigenvector `x = s + q` with `s ∈ S`,
`q ∈ Q` has `s` and `q` again eigenvectors.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section
open scoped BigOperators TensorProduct

namespace Submission.E8Decomp

open Submission.E8Tensor Submission.E8TensorBound Submission.VermaWeight
open Submission.E8WeightSpaces
open UniversalEnvelopingAlgebra

variable {N : Submodule U V}

variable [Module.Finite ℂ (T N)]

/-- The Cartan action on `T N` is the enveloping-algebra action of the Chevalley generator. -/
lemma deriv_h_eq_iota (j : Fin 8) (x : T N) :
    Submission.E8Tensor.deriv (N := N) (Submission.E8Weights.SerreH j) x = (ι ℂ (Submission.E8Weights.SerreH j)) • x :=
  (iota_smul_eq_deriv (N := N) (Submission.E8Weights.SerreH j) x).symm

/-- **The weight space of a direct sum of `U`-submodules.**  If `S ⊔ Q = P` and `S ⊓ Q = ⊥` then
`TLwt ν ⊓ P = (TLwt ν ⊓ S) ⊔ (TLwt ν ⊓ Q)`. -/
theorem TLwt_inf_sup {S Q P : Submodule U (T N)} (hsup : S ⊔ Q = P) (hinf : S ⊓ Q = ⊥)
    (ν : Fin 8 → ℤ) :
    P.restrictScalars ℂ ⊓ TLwt N ν
      = (S.restrictScalars ℂ ⊓ TLwt N ν) ⊔ (Q.restrictScalars ℂ ⊓ TLwt N ν) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxP, hxT⟩ := Submodule.mem_inf.mp hx
    rw [← hsup] at hxP
    obtain ⟨s, hs, q, hq, hsq⟩ := Submodule.mem_sup.mp hxP
    have hsm : ∀ c : ℂ, c • s ∈ S := fun c => by
      rw [← Submission.Enveloping.algebraMap_smul_eq (R := ℂ) (L := LieAlgebra.e₈ ℂ) c s]
      exact S.smul_mem _ hs
    have hqm : ∀ c : ℂ, c • q ∈ Q := fun c => by
      rw [← Submission.Enveloping.algebraMap_smul_eq (R := ℂ) (L := LieAlgebra.e₈ ℂ) c q]
      exact Q.smul_mem _ hq
    have hsT : s ∈ TLwt N ν := by
      refine mem_TLwt_of_deriv_h_eq (N := N) ν s fun j => ?_
      have h1 : Submission.E8Tensor.deriv (N := N) (Submission.E8Weights.SerreH j) s
            + Submission.E8Tensor.deriv (N := N) (Submission.E8Weights.SerreH j) q
          = (((ν j : ℤ)) : ℂ) • s + (((ν j : ℤ)) : ℂ) • q := by
        rw [← map_add, hsq, deriv_h_eq_of_mem_TLwt (N := N) j hxT]
        rw [← hsq, smul_add]
      have h2 : Submission.E8Tensor.deriv (N := N) (Submission.E8Weights.SerreH j) s
            - (((ν j : ℤ)) : ℂ) • s
          = -(Submission.E8Tensor.deriv (N := N) (Submission.E8Weights.SerreH j) q
              - (((ν j : ℤ)) : ℂ) • q) := by
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, h1, add_comm]
      have hS1 : Submission.E8Tensor.deriv (N := N) (Submission.E8Weights.SerreH j) s ∈ S := by
        rw [deriv_h_eq_iota]; exact S.smul_mem _ hs
      have hQ1 : Submission.E8Tensor.deriv (N := N) (Submission.E8Weights.SerreH j) q ∈ Q := by
        rw [deriv_h_eq_iota]; exact Q.smul_mem _ hq
      have hmem : Submission.E8Tensor.deriv (N := N) (Submission.E8Weights.SerreH j) s
            - (((ν j : ℤ)) : ℂ) • s ∈ S ⊓ Q :=
        Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hS1 (hsm _), by
          rw [h2]; exact Submodule.neg_mem _ (Submodule.sub_mem _ hQ1 (hqm _))⟩
      rw [hinf] at hmem
      rw [Submodule.mem_bot, sub_eq_zero] at hmem
      exact hmem
    have hqT : q ∈ TLwt N ν := by
      refine mem_TLwt_of_deriv_h_eq (N := N) ν q fun j => ?_
      have h2 := deriv_h_eq_of_mem_TLwt (N := N) j hxT
      rw [← hsq, map_add, deriv_h_eq_of_mem_TLwt (N := N) j hsT, smul_add] at h2
      exact add_left_cancel h2
    exact Submodule.mem_sup.mpr ⟨s, Submodule.mem_inf.mpr ⟨hs, hsT⟩, q,
      Submodule.mem_inf.mpr ⟨hq, hqT⟩, hsq⟩
  · refine sup_le (le_inf ?_ inf_le_right) (le_inf ?_ inf_le_right)
    · rw [← hsup, Submodule.restrictScalars_sup]; exact le_trans inf_le_left le_sup_left
    · rw [← hsup, Submodule.restrictScalars_sup]; exact le_trans inf_le_left le_sup_right

/-- **Additivity of the weight multiplicity over a direct sum.** -/
theorem finrank_inf_add {S Q P : Submodule U (T N)} (hsup : S ⊔ Q = P) (hinf : S ⊓ Q = ⊥)
    (ν : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(Submission.E8ConstChar.restr P ⊓ TLwt N ν)
      = Module.finrank ℂ ↥(Submission.E8ConstChar.restr S ⊓ TLwt N ν)
        + Module.finrank ℂ ↥(Submission.E8ConstChar.restr Q ⊓ TLwt N ν) := by
  set A : Submodule ℂ (T N) := Submission.E8ConstChar.restr S ⊓ TLwt N ν with hA
  set B : Submodule ℂ (T N) := Submission.E8ConstChar.restr Q ⊓ TLwt N ν with hB
  have hkey2 : A ⊓ B = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    have hxS : x ∈ S :=
      (Submodule.restrictScalars_mem ℂ S x).mp (Submodule.mem_inf.mp (hA ▸ hx1)).1
    have hxQ : x ∈ Q :=
      (Submodule.restrictScalars_mem ℂ Q x).mp (Submodule.mem_inf.mp (hB ▸ hx2)).1
    have hxSQ : x ∈ S ⊓ Q := Submodule.mem_inf.mpr ⟨hxS, hxQ⟩
    rw [hinf, Submodule.mem_bot] at hxSQ
    exact hxSQ
  have hsup' : Submission.E8ConstChar.restr P ⊓ TLwt N ν = A ⊔ B := by
    rw [hA, hB]; exact TLwt_inf_sup hsup hinf ν
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [← hsup', hkey2, finrank_bot, add_zero] at h
  rw [hA, hB] at h
  exact h

/-- The dimension form: `finrank P = finrank S + finrank Q` for `S ⊔ Q = P`, `S ⊓ Q = ⊥`. -/
theorem finrank_eq_add {S Q P : Submodule U (T N)} (hsup : S ⊔ Q = P) (hinf : S ⊓ Q = ⊥) :
    Module.finrank ℂ ↥(Submission.E8ConstChar.restr P)
      = Module.finrank ℂ ↥(Submission.E8ConstChar.restr S)
        + Module.finrank ℂ ↥(Submission.E8ConstChar.restr Q) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (Submission.E8ConstChar.restr S) (Submission.E8ConstChar.restr Q)
  have h2 : (Submission.E8ConstChar.restr S ⊓ Submission.E8ConstChar.restr Q) = ⊥ := by
    rw [← Submodule.restrictScalars_inf, hinf]; rfl
  rw [← Submodule.restrictScalars_sup, hsup, h2, finrank_bot, add_zero] at h
  exact h

/-- **The character decomposition of a `U`-submodule of `T N`.**  Every `U`-submodule `P ≤ T N` is
the (internal) direct sum of finitely many simple submodules, and the weight multiplicities add. -/
theorem exists_simples_decomp (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (P : Submodule U (T N)) :
    ∃ (l : List (Submodule U (T N))),
      (∀ S ∈ l, IsSimpleModule U S) ∧ (∀ S ∈ l, S ≤ P) ∧
      (∀ ν : Fin 8 → ℤ,
        Submission.E8ConstChar.chFun N P ν
          = (l.map (fun S => Submission.E8ConstChar.chFun N S ν)).sum) := by
  classical
  haveI hss : IsSemisimpleModule U (T N) := isSemisimple_tensor N hvN hmax
  haveI hfin : Module.Finite ℂ (T N) := finite_tensor N hvN hmax
  suffices H : ∀ n : ℕ, ∀ P : Submodule U (T N),
      Module.finrank ℂ ↥(Submission.E8ConstChar.restr P) = n →
      ∃ (l : List (Submodule U (T N))),
        (∀ S ∈ l, IsSimpleModule U S) ∧ (∀ S ∈ l, S ≤ P) ∧
        (∀ ν : Fin 8 → ℤ,
          Submission.E8ConstChar.chFun N P ν
            = (l.map (fun S => Submission.E8ConstChar.chFun N S ν)).sum) by
    exact H _ P rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hPn
    by_cases hbot : P = ⊥
    · refine ⟨[], by simp, by simp, fun ν => ?_⟩
      rw [hbot, List.map_nil, List.sum_nil, Submission.E8ConstChar.chFun,
        show Submission.E8ConstChar.restr (⊥ : Submodule U (T N)) = (⊥ : Submodule ℂ (T N))
          from rfl, bot_inf_eq, finrank_bot]
      norm_num
    · obtain ⟨S, hSle, hS⟩ :=
        (IsSemisimpleModule.eq_bot_or_exists_simple_le (M := T N) P).resolve_left hbot
      obtain ⟨Q₀, hQ₀⟩ := ComplementedLattice.exists_isCompl S
      have hQsup : S ⊔ Q₀ = ⊤ := codisjoint_iff.mp hQ₀.codisjoint
      have hQdis : Disjoint S Q₀ := hQ₀.disjoint
      set Q : Submodule U (T N) := Q₀ ⊓ P with hQ
      have hsup : S ⊔ Q = P := by
        refine le_antisymm ?_ ?_
        · refine sup_le hSle ?_
          rw [hQ]; exact inf_le_right
        · intro x hx
          have hx1 : x ∈ S ⊔ Q₀ := by rw [hQsup]; trivial
          obtain ⟨s, hs, q, hq, hsq⟩ := Submodule.mem_sup.mp hx1
          have hqP : q ∈ P := by
            have : q = x - s := by rw [← hsq]; abel
            rw [this]; exact Submodule.sub_mem _ hx (hSle hs)
          exact Submodule.mem_sup.mpr ⟨s, hs, q,
            Submodule.mem_inf.mpr ⟨hq, hqP⟩, hsq⟩
      have hinf : S ⊓ Q = ⊥ := by
        rw [eq_bot_iff, hQ]
        exact le_trans (inf_le_inf_left S inf_le_left) hQdis.le_bot
      have hdim := finrank_eq_add hsup hinf
      have hSpos : 0 < Module.finrank ℂ ↥(Submission.E8ConstChar.restr S) := by
        haveI : Nontrivial ↥(Submission.E8ConstChar.restr S) := hS.nontrivial
        exact Module.finrank_pos
      have hlt : Module.finrank ℂ ↥(Submission.E8ConstChar.restr Q) < n := by
        rw [hPn] at hdim; omega
      obtain ⟨l, hsimp, hle, hsum⟩ := ih _ hlt Q rfl
      refine ⟨S :: l, ?_, ?_, fun ν => ?_⟩
      · intro T hT
        rcases List.mem_cons.mp hT with rfl | hT
        · exact hS
        · exact hsimp T hT
      · intro T hT
        rcases List.mem_cons.mp hT with rfl | hT
        · exact hSle
        · exact le_trans (hle T hT) inf_le_right
      · rw [List.map_cons, List.sum_cons, ← hsum ν]
        rw [Submission.E8ConstChar.chFun, Submission.E8ConstChar.chFun,
          Submission.E8ConstChar.chFun, finrank_inf_add hsup hinf ν]
        push_cast
        ring

/-- **The character decomposition of the tensor square.**  The character of `T N` is the sum of the
characters of the simple constituents of a direct-sum decomposition of `T N`. -/
theorem chT_eq_sum_chFun (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) :
    ∃ (l : List (Submodule U (T N))),
      (∀ S ∈ l, IsSimpleModule U S) ∧
      (∀ ν : Fin 8 → ℤ,
        (Module.finrank ℂ ↥(TLwt N ν) : ℚ)
          = (l.map (fun S => Submission.E8ConstChar.chFun N S ν)).sum) := by
  classical
  haveI hss : IsSemisimpleModule U (T N) := isSemisimple_tensor N hvN hmax
  haveI hfin : Module.Finite ℂ (T N) := finite_tensor N hvN hmax
  obtain ⟨l, hsimp, -, hsum⟩ := exists_simples_decomp N hvN hmax ⊤
  refine ⟨l, hsimp, fun ν => ?_⟩
  have h := hsum ν
  rw [Submission.E8ConstChar.chFun,
    show Submission.E8ConstChar.restr (⊤ : Submodule U (T N)) = (⊤ : Submodule ℂ (T N))
      from rfl, top_inf_eq] at h
  exact h

end Submission.E8Decomp
