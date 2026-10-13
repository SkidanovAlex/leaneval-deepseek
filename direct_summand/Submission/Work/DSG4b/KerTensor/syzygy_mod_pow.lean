import Mathlib
import Submission.Work.DSM2b.FlatSetup
import Submission.Work.DSM2b.assembly_aux
import Submission.Work.DSM2bA.syzygy_mod_pow
import Submission.Work.DSM1p.Assembly.flat_completion
import Submission.Work.DSG4b.KerTensor.coordBase_eq_zero_of_mem_map
import Submission.Work.DSG4b.KerTensor.exists_sub_mem_smul_top_of_mem_spanBase

namespace Work.DSG4b.KerTensor

universe u

/-!
# Syzygies modulo `I ^ n` for an arbitrary ideal `I`

This file proves `Work.DSG4b.KerTensor.syzygy_mod_pow`, the general-ideal form of
`Work.DSM2bA.syzygy_mod_pow` (which treats a principal ideal `(π)`).

The proof uses the general-ideal pieces proved in the sibling files:

* `Work.DSG4b.KerTensor.coordBase_eq_zero_of_mem_map`: the hypothesis `hy` says that the base
  change of `coordBase g` to `S = R ⧸ I ^ n` and `M = B ⧸ I ^ n B` kills the class of `y`;
* `Work.DSM2bA.flat_ker_le_spanBase`: flatness of `M` over `S` converts this vanishing into a
  membership in `spanBase (ker gS)`;
* `Work.DSG4b.KerTensor.exists_sub_mem_smul_top_of_mem_spanBase`: base change plus elementwise
  Artin–Rees turns that membership into `w ∈ spanBase (ker g)` with the prescribed error;
* the final lifting step along `B ↠ B ⧸ I ^ n B` is done inline (`hstep` below).
-/

/-- **Syzygies modulo `I ^ n`, with Artin–Rees loss (general ideal).** `R` a commutative ring,
`I ⊆ R` an ideal, `B` an `R`-algebra, `g : R^k → R^m` a map of coordinate modules, `c` a constant
witnessing elementwise Artin–Rees for `g` and `I` in the form "`g x ∈ I^N` coordinatewise implies
`x` lies in `ker g + I^(N-c) R^k`", and `B ⧸ I^n B` flat over `R ⧸ I^n R` for all `n`. Then any
`y : B^k` whose image under the base-changed map `Work.DSM2b.coordBase g` lies in `I^n B^m`
coordinatewise differs from an element of `Work.DSM2b.spanBase (ker g)` by an element of
`I^(n-c) B^k`. This is `Work.DSM2bA.syzygy_mod_pow` with the principal ideal `(π)` replaced by an
arbitrary ideal `I` of `R` (the `π ^ (n-c) • z` correction is replaced by `z ∈ I ^ (n-c) • ⊤`).
Proof: reduce modulo `I^n`, use flatness of `B ⧸ I^n B` over `R ⧸ I^n` to compute kernels after base
change (`Module.Flat.lTensor_exact`), rewrite with `Work.DSM2b.spanBase`, and lift back with the
elementwise Artin–Rees input. -/
theorem syzygy_mod_pow {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) {k m : ℕ} (g : (Fin k → R) →ₗ[R] (Fin m → R)) (c : ℕ)
    (hAR : ∀ n (x : Fin k → R), (∀ i, g x i ∈ I ^ n) →
      ∃ z ∈ I ^ (n - c) • (⊤ : Submodule R (Fin k → R)), x - z ∈ LinearMap.ker g)
    (hflat : ∀ n : ℕ, Module.Flat (R ⧸ I ^ n) (B ⧸ (I ^ n).map (algebraMap R B)))
    (n : ℕ) {y : Fin k → B}
    (hy : ∀ i, Work.DSM2b.coordBase g y i ∈ (I ^ n).map (algebraMap R B)) :
    ∃ w : Fin k → B, w ∈ Work.DSM2b.spanBase (LinearMap.ker g) ∧
      ∀ i, (y - w) i ∈ (I ^ (n - c)).map (algebraMap R B) := by
  classical
  -- The class of `y` is killed by the base change of `coordBase g` to the quotients.
  have hz := coordBase_eq_zero_of_mem_map (R := R) (B := B) I g n hy
  -- Flatness of `B ⧸ I ^ n B` over `R ⧸ I ^ n` puts that class in the span of the syzygies
  -- of the base changed map.
  have hzmem : (fun j => Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)) (y j)) ∈
      Work.DSM2b.spanBase (R := R ⧸ I ^ n) (B := B ⧸ (I ^ n).map (algebraMap R B))
        (LinearMap.ker (Work.DSM2b.coordBase (R := R) (B := R ⧸ I ^ n) g)) :=
    Work.DSM2bA.flat_ker_le_spanBase (S := R ⧸ I ^ n)
      (M := B ⧸ (I ^ n).map (algebraMap R B)) (hflat n)
      (Work.DSM2b.coordBase (R := R) (B := R ⧸ I ^ n) g)
      (fun j => Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)) (y j)) hz
  -- Base change + Artin–Rees: the class of `y` is the class of an element of `spanBase (ker g)`
  -- up to `I ^ (n - c)`.
  obtain ⟨w, hw, herr⟩ :=
    exists_sub_mem_smul_top_of_mem_spanBase (R := R) (B := B) I g c n hAR hzmem
  refine ⟨w, hw, fun i => ?_⟩
  have hpt : Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)) (y i) -
        Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)) (w i) ∈
      Ideal.map (algebraMap R (B ⧸ (I ^ n).map (algebraMap R B))) (I ^ (n - c)) := by
    have h := (Work.DSM2b.mem_smul_top_fin_iff
      (Ideal.map (algebraMap R (B ⧸ (I ^ n).map (algebraMap R B))) (I ^ (n - c)))
      ((fun j => Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)) (y j)) -
        (fun j => Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)) (w j)))).mp herr i
    simpa using h
  -- Final lifting step: an element of `I ^ (n - c) • (B ⧸ I ^ n B)^k` for the class of `y i - w i`
  -- forces `y i - w i ∈ I ^ (n - c) B`.
  have hstep : ∀ a b : B,
      Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)) a -
          Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)) b ∈
        Ideal.map (algebraMap R (B ⧸ (I ^ n).map (algebraMap R B))) (I ^ (n - c)) →
      a - b ∈ (I ^ (n - c)).map (algebraMap R B) := by
    intro a b hab
    -- the two descriptions of the error ideal agree
    have hcomp : algebraMap R (B ⧸ (I ^ n).map (algebraMap R B)) =
        (Ideal.Quotient.mk ((I ^ n).map (algebraMap R B))).comp (algebraMap R B) :=
      IsScalarTower.algebraMap_eq R B (B ⧸ (I ^ n).map (algebraMap R B))
    have hmap : Ideal.map (algebraMap R (B ⧸ (I ^ n).map (algebraMap R B))) (I ^ (n - c)) =
        Ideal.map (Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)))
          ((I ^ (n - c)).map (algebraMap R B)) := by
      rw [hcomp, Ideal.map_map]
    have h1 : Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)) (a - b) ∈
        Ideal.map (Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)))
          ((I ^ (n - c)).map (algebraMap R B)) := by
      rw [← map_sub, hmap] at hab
      exact hab
    -- lift the class of `a - b` to an element of `I ^ (n - c) B`
    obtain ⟨s, hs, hsm⟩ := (Ideal.mem_map_iff_of_surjective
      (Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)))
      Ideal.Quotient.mk_surjective).mp h1
    have hsub : a - b - s ∈ (I ^ n).map (algebraMap R B) :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem (a - b) s).mp hsm.symm
    have hJK : (I ^ n).map (algebraMap R B) ≤ (I ^ (n - c)).map (algebraMap R B) :=
      Ideal.map_mono (Ideal.pow_le_pow_right (Nat.sub_le n c))
    have heq : a - b = s + (a - b - s) := by abel
    rw [heq]
    exact Ideal.add_mem _ hs (hJK hsub)
  have h := hstep (y i) (w i) hpt
  simpa using h

end Work.DSG4b.KerTensor
