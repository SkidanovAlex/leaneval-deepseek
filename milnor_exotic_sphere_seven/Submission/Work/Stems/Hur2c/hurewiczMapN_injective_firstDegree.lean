import Submission.Work.Stems.Hur2c.hurewiczMapN_injective_of_degen_cycle
import Submission.Work.Stems.Hur2c.psiLinGen_degen_cycle
import Submission.Work.RatHurewicz.fillingFamilyConst
import Submission.Work.Stems.HurewiczNeutralAgree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Injectivity of the Hurewicz map in the first non-vanishing degree

**Unconditional** form, all degrees `n ≥ 2`: for `X` with `π_i(X,x₀) = 0` for `i < n`, the
Hurewicz map `Work.Stems.hurewiczMapN n … x₀ : π_n(X,x₀) → H_n(X;ℤ)` is injective.

The ingredients are all in place:

* the chain-level bridge `Work.RatHurewicz.cubicalBridgeDeg`;
* **(Z)** `Work.Stems.Hur2c.psiLinGen_single_based` and **(Y)**
  `Work.Stems.Hur2c.psiLinGen_cubD_eq_zero` for the linearised `Ψ` of `Work.RatHurewicz.psiDefs`;
* **(E)** `Work.Stems.Hur2c.psiLinGen_degen_cycle` ("`Ψ` kills degenerate `n`-cycles", the general
  `T`-calculus of `Submission/Work/Stems/PSI_DEG_NOTES.md`);
* the **assembly** `Work.Stems.Hur2c.hurewiczMapN_injective_of_degen_cycle`;
* the existence of a filling family from connectivity
  (`Work.RatHurewicz.fillingFamilyConst`).

This is the injectivity half of the classical Hurewicz isomorphism in the first non-vanishing
degree (`Work.Stems.hurewicz_first_degree`, `Submission/Work/Stems/HurewiczFirstDegree.lean`), in
the fork-neutral `hurewiczMapN` vocabulary.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.Stems.Hur2c

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **An on-the-nose injectivity statement**: a class whose Hurewicz image vanishes is the class of
the constant cube. -/
theorem hurewiczMapN_eq_const_of_eq_zero (n : ℕ) (hn : 2 ≤ n) (x₀ : X)
    (hconn : ∀ i : ℕ, i < n → Subsingleton (HomotopyGroup (Fin i) X x₀))
    (a : HomotopyGroup (Fin n) X x₀)
    (ha : Work.Stems.hurewiczMapN n (by omega) x₀ a = 0) :
    a = ⟦GenLoop.const⟧ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  haveI : Nontrivial (Fin (k + 2)) :=
    ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by intro h; simpa using congrArg Fin.val h⟩⟩
  -- a filling family up to level `k+1`
  obtain ⟨Kf, hα, hβ, hγ⟩ := Work.RatHurewicz.fillingFamilyConst (k + 1) x₀
    (fun i hi => hconn i (by omega))
  let K : Work.RatHurewicz.Tower x₀ (k + 1) := ⟨Kf, hα, hβ, hγ⟩
  have hmain : (⟦Quotient.out a⟧ : HomotopyGroup (Fin (k + 2)) X x₀) = ⟦GenLoop.const⟧ := by
    refine Work.Stems.Hur2c.hurewiczMapN_injective_of_degen_cycle (k + 1) k K le_rfl ?_
      (Quotient.out a) ?_
    · -- **(E)**
      intro d hd hcyc
      exact Work.Stems.Hur2c.psiLinGen_degen_cycle (k + 1) k
        (fun i hi => hconn i (by omega)) K le_rfl d hd hcyc
    · rw [Quotient.out_eq a]
      exact ha
  rw [← Quotient.out_eq a]
  exact hmain

/-- **The Hurewicz map is injective** in the first non-vanishing degree, all degrees. -/
theorem hurewiczMapN_injective_firstDegree (n : ℕ) (hn : 2 ≤ n) (x₀ : X)
    (hconn : ∀ i : ℕ, i < n → Subsingleton (HomotopyGroup (Fin i) X x₀)) :
    Function.Injective (Work.Stems.hurewiczMapN n (by omega) x₀) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  haveI : Nontrivial (Fin (k + 2)) :=
    ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by intro h; simpa using congrArg Fin.val h⟩⟩
  letI : Group (HomotopyGroup (Fin (k + 2)) X x₀) := HomotopyGroup.group (Fin (k + 2))
  intro a b hab
  -- the vanishing of the Hurewicz image of `a * b⁻¹`
  have hzero : Work.Stems.hurewiczMapN (k + 2) (by omega) x₀ (a * b⁻¹) = 0 := by
    have h1 : Work.Stems.hurewiczHom (k + 1) x₀ (Additive.ofMul a) =
        Work.Stems.hurewiczMapN (k + 2) (by omega) x₀ a :=
      Work.Stems.hurewiczHom_eq_hurewiczMapN (k + 1) x₀ (Additive.ofMul a)
    have h2 : Work.Stems.hurewiczHom (k + 1) x₀ (Additive.ofMul b) =
        Work.Stems.hurewiczMapN (k + 2) (by omega) x₀ b :=
      Work.Stems.hurewiczHom_eq_hurewiczMapN (k + 1) x₀ (Additive.ofMul b)
    have hsub : (Additive.ofMul a - Additive.ofMul b :
        Additive (HomotopyGroup (Fin (k + 2)) X x₀)) = Additive.ofMul (a * b⁻¹) := by
      rw [ofMul_mul, ofMul_inv, sub_eq_add_neg]
    have h3 : Work.Stems.hurewiczHom (k + 1) x₀ (Additive.ofMul (a * b⁻¹)) =
        Work.Stems.hurewiczMapN (k + 2) (by omega) x₀ (a * b⁻¹) :=
      Work.Stems.hurewiczHom_eq_hurewiczMapN (k + 1) x₀ (Additive.ofMul (a * b⁻¹))
    rw [← h3, ← hsub, map_sub, h1, h2, hab, sub_self]
  have hkey := hurewiczMapN_eq_const_of_eq_zero (k + 2) hn x₀ hconn (a * b⁻¹) hzero
  rw [← HomotopyGroup.one_def] at hkey
  have hmul : a = (a * b⁻¹) * b := by rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [hmul, hkey, one_mul]

/-- **The Hurewicz image is torsion only for torsion classes** — the form in which blueprint step
**S1** (`Submission/Work/Drive/SERRE_BLUEPRINT.md`) consumes the theorem: for `X` with
`π_i(X,x₀) = 0` for `i < k+2` and a class `a ∈ π_{k+2}(X,x₀)` whose Hurewicz image has finite order,
`a` itself has finite order.  (Stated for the successor form `k+2` so that the group structure on
`HomotopyGroup (Fin (k+2))` is found by type class search.) -/
theorem hurewiczMapN_torsion_of_torsion_image (k : ℕ) (x₀ : X)
    (hconn : ∀ i : ℕ, i < k + 2 → Subsingleton (HomotopyGroup (Fin i) X x₀))
    (a : HomotopyGroup (Fin (k + 2)) X x₀)
    (ha : ∃ M : ℕ, 0 < M ∧
      M • Work.Stems.hurewiczMapN (k + 2) (by omega) x₀ a = 0) :
    ∃ M : ℕ, 0 < M ∧ a ^ M = 1 := by
  obtain ⟨M, hM, hMa⟩ := ha
  have hpow : Work.Stems.hurewiczMapN (k + 2) (by omega) x₀ (a ^ M) = 0 := by
    have h1 : Additive.ofMul (a ^ M) = M • Additive.ofMul a := ofMul_pow M a
    have h2 : Work.Stems.hurewiczHom (k + 1) x₀ (M • Additive.ofMul a) =
        M • Work.Stems.hurewiczHom (k + 1) x₀ (Additive.ofMul a) := map_nsmul _ M _
    have h3 : Work.Stems.hurewiczHom (k + 1) x₀ (Additive.ofMul a) =
        Work.Stems.hurewiczMapN (k + 2) (by omega) x₀ a :=
      Work.Stems.hurewiczHom_eq_hurewiczMapN (k + 1) x₀ (Additive.ofMul a)
    have h4 : Work.Stems.hurewiczMapN (k + 1 + 1) (by omega) x₀ (a ^ M) =
        Work.Stems.hurewiczHom (k + 1) x₀ (Additive.ofMul (a ^ M)) := by
      simpa using (Work.Stems.hurewiczHom_eq_hurewiczMapN (k + 1) x₀
        (Additive.ofMul (a ^ M))).symm
    have hbridge : Work.Stems.hurewiczMapN (k + 2) (by omega) x₀ (a ^ M) =
        Work.Stems.hurewiczMapN (k + 1 + 1) (by omega) x₀ (a ^ M) := rfl
    rw [hbridge, h4, h1, h2, h3, hMa]
  exact ⟨M, hM, hurewiczMapN_eq_const_of_eq_zero (k + 2) (by omega) x₀ hconn (a ^ M) hpow⟩

end

end Work.Stems.Hur2c
