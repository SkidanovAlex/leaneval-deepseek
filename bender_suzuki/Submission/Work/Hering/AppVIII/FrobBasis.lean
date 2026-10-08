/-
# Additive maps of a finite field of characteristic two are linearized polynomials

For a finite field `E` of characteristic two with `|E| = 2 ^ d`, every additive map `E → E` is
uniquely of the form `x ↦ ∑ i, c i * x ^ (2^i)` (`i : Fin d`) — the classical expansion of
`𝔽₂`-linear maps in the Frobenius powers (Ore's theorem on linearized polynomials), which is
Lemma 2 a) of App. VIII of Peterfalvi I.
-/
import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

noncomputable section

open Polynomial Module

namespace Work.Hering.AppVIII

/-- **Frobenius expansion of an additive map.**  Every additive map `f : E → E` on a finite field
`E` of characteristic two with `|E| = 2 ^ d` is uniquely `f x = ∑ i, c i * x ^ (2 ^ i)`. -/
theorem frobExpansion {E : Type*} [Field E] [CharP E 2] [Fintype E] {d : ℕ}
    (hd : Fintype.card E = 2 ^ d) (f : E →+ E) :
    ∃! c : Fin d → E, ∀ x : E, f x = ∑ i, c i * x ^ (2 ^ (i : ℕ)) := by
  classical
  -- ## the `ZMod 2`-module structure of `E`
  letI : Module (ZMod 2) E := AddCommGroup.zmodModule (fun x => by
    rw [two_nsmul]; exact CharTwo.add_self_eq_zero x)
  have hfr : Module.finrank (ZMod 2) E = d := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)
    rw [Nat.card_zmod] at h
    have h2 : 2 ^ d = 2 ^ Module.finrank (ZMod 2) E := by
      rw [← hd, ← Nat.card_eq_fintype_card]
      exact h
    exact (Nat.pow_right_injective (by norm_num) h2).symm
  -- ## Frobenius additivity
  have hpow : ∀ i : ℕ, ∀ x y : E, (x + y) ^ (2 ^ i) = x ^ (2 ^ i) + y ^ (2 ^ i) := fun i x y =>
    add_pow_char_pow (p := 2) (n := i) (x := x) (y := y)
  have hsum_add : ∀ (c : Fin d → E) (x y : E),
      (∑ i, c i * (x + y) ^ (2 ^ (i : ℕ)))
        = (∑ i, c i * x ^ (2 ^ (i : ℕ))) + ∑ i, c i * y ^ (2 ^ (i : ℕ)) := by
    intro c x y
    have hterm : ∀ i : Fin d, c i * (x + y) ^ (2 ^ (i : ℕ))
        = c i * x ^ (2 ^ (i : ℕ)) + c i * y ^ (2 ^ (i : ℕ)) := by
      intro i
      rw [hpow (i : ℕ) x y, mul_add]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
  -- ## the map `Φ`
  let Φ : (Fin d → E) → (E →+ E) := fun c =>
    AddMonoidHom.mk' (fun x : E => ∑ i, c i * x ^ (2 ^ (i : ℕ))) (hsum_add c)
  have hΦapply : ∀ (c : Fin d → E) (x : E), Φ c x = ∑ i, c i * x ^ (2 ^ (i : ℕ)) :=
    fun c x => rfl
  -- ## `Φ` is injective
  have hinj : Function.Injective Φ := by
    intro c c' hcc
    have hpoint : ∀ x : E, ∑ j, c j * x ^ (2 ^ (j : ℕ)) = ∑ j, c' j * x ^ (2 ^ (j : ℕ)) := by
      intro x
      rw [← hΦapply c x, ← hΦapply c' x, hcc]
    funext i
    have hcoeff : c i + c' i = 0 := by
      set P : E[X] := ∑ j : Fin d, C (c j + c' j) * X ^ (2 ^ (j : ℕ)) with hP
      have hPzero : P = 0 := by
        refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P Finset.univ ?_ ?_
        · intro x _
          have heval : ∀ s : Finset (Fin d),
              (∑ j ∈ s, C (c j + c' j) * X ^ (2 ^ (j : ℕ)) : E[X]).eval x
                = ∑ j ∈ s, (c j + c' j) * x ^ (2 ^ (j : ℕ)) := by
            intro s
            induction s using Finset.induction_on with
            | empty => simp
            | insert j s hj ih =>
                simp only [Finset.sum_insert hj, ih, Polynomial.eval_add, Polynomial.eval_mul,
                  Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
          rw [hP, heval Finset.univ]
          have hterm : ∀ j : Fin d, (c j + c' j) * x ^ (2 ^ (j : ℕ))
              = c j * x ^ (2 ^ (j : ℕ)) + c' j * x ^ (2 ^ (j : ℕ)) := fun j =>
            add_mul (c j) (c' j) (x ^ (2 ^ (j : ℕ)))
          rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib]
          rw [hpoint x, CharTwo.add_self_eq_zero]
        · have hd1 : 1 ≤ d := by
            rcases Nat.eq_zero_or_pos d with h | h
            · subst h
              simp at hd
              exact absurd hd (by have := Fintype.one_lt_card (α := E); omega)
            · exact h
          have hle : P.natDegree ≤ 2 ^ (d - 1) := by
            rw [hP]
            refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ) (n := 2 ^ (d - 1))
              _ fun j _ => ?_
            refine (Polynomial.natDegree_C_mul_X_pow_le (c j + c' j) (2 ^ (j : ℕ))).trans ?_
            refine Nat.pow_le_pow_right (by norm_num) ?_
            have := j.isLt
            omega
          calc P.natDegree ≤ 2 ^ (d - 1) := hle
            _ < 2 ^ d := Nat.pow_lt_pow_right (by norm_num) (by omega)
            _ = Fintype.card E := hd.symm
      have hc := congrArg (fun p : E[X] => p.coeff (2 ^ (i : ℕ))) hPzero
      simp only [Polynomial.coeff_zero] at hc
      rw [hP, Polynomial.finsetSum_coeff] at hc
      rw [Finset.sum_eq_single i] at hc
      · have hsplit : (C (c i + c' i) * X ^ (2 ^ (i : ℕ)) : E[X])
            = C (c i) * X ^ (2 ^ (i : ℕ)) + C (c' i) * X ^ (2 ^ (i : ℕ)) := by
          rw [show (C (c i + c' i) : E[X]) = C (c i) + C (c' i) from
            map_add C (c i) (c' i), add_mul]
        rw [hsplit, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
          Polynomial.coeff_C_mul_X_pow] at hc
        simpa using hc
      · intro j _ hj
        rw [Polynomial.coeff_C_mul_X_pow, if_neg]
        intro hcon
        exact hj (Fin.ext (Nat.pow_right_injective (by norm_num) hcon.symm))
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    have h2 : c i + c' i = c i + c i := by rw [hcoeff, CharTwo.add_self_eq_zero]
    exact (add_left_cancel h2).symm
  -- ## an injection in the other direction
  obtain ⟨b⟩ : Nonempty (Basis (Fin d) (ZMod 2) E) :=
    ⟨Module.finBasisOfFinrankEq (R := ZMod 2) (M := E) hfr⟩
  have hres : Function.Injective (fun f : E →+ E => fun i : Fin d => f (b i)) := by
    intro f g hfg
    refine AddMonoidHom.toZModLinearMap_injective (n := 2) ?_
    exact b.ext fun i => congrFun hfg i
  letI : Fintype (E →+ E) :=
    Fintype.ofInjective (fun f : E →+ E => fun i : Fin d => f (b i)) hres
  have hcardEq : Fintype.card (Fin d → E) = Fintype.card (E →+ E) :=
    le_antisymm (Fintype.card_le_of_injective Φ hinj) (Fintype.card_le_of_injective _ hres)
  have hsurj : Function.Surjective Φ :=
    (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcardEq)).mp hinj
  -- ## conclusion
  obtain ⟨c, hc⟩ := hsurj f
  have hcf : ∀ x : E, f x = ∑ i, c i * x ^ (2 ^ (i : ℕ)) := by
    intro x
    rw [← hΦapply c x]
    exact (DFunLike.congr_fun hc x).symm
  refine ⟨c, hcf, ?_⟩
  intro c' hc'
  have hcc' : Φ c' = Φ c := by
    ext x
    rw [hΦapply c' x, hΦapply c x, (hc' x).symm, hcf x]
  exact hinj hcc'

end Work.Hering.AppVIII
