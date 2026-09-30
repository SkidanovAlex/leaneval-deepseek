import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

set_option maxHeartbeats 16000000 in
theorem circuit_hmin_subfamily {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℚ V] (x : V)
    (g : Fin n → V)
    (hg : LinearIndependent ℚ g)
    (hx : ∀ b : Fin n, x ∉ Submodule.span ℚ (Set.range (fun b' : {b' : Fin n // (b' : Fin n) ≠ b} => g b'))) :
    ∀ a : Fin (n + 1),
      LinearIndependent ℚ (fun j : {j : Fin (n + 1) // j ≠ a} =>
        (@Fin.cons n (fun _ => V) x g) (j : Fin (n + 1))) := by
  intro a
  induction a using Fin.cases with
  | zero =>
      have hf : Function.Injective (fun j : {j : Fin (n + 1) // j ≠ 0} => Fin.pred j.1 j.2) := by
        intro j j' h
        have h2 : (Fin.pred j.1 j.2).succ = (Fin.pred j'.1 j'.2).succ := congrArg Fin.succ h
        rw [Fin.succ_pred j.1 j.2, Fin.succ_pred j'.1 j'.2] at h2
        exact Subtype.ext h2
      have hcomp : LinearIndependent ℚ (fun j : {j : Fin (n + 1) // j ≠ 0} => g (Fin.pred j.1 j.2)) :=
        hg.comp (fun j : {j : Fin (n + 1) // j ≠ 0} => Fin.pred j.1 j.2) hf
      have hfun : (fun j : {j : Fin (n + 1) // j ≠ 0} => g (Fin.pred j.1 j.2)) =
          (fun j : {j : Fin (n + 1) // j ≠ 0} => (@Fin.cons n (fun _ => V) x g) j.1) := by
        funext j
        conv_rhs => rw [← Fin.succ_pred j.1 j.2]
        rw [Fin.cons_succ]
      rw [← hfun]
      exact hcomp
  | succ k =>
      have hk : LinearIndependent ℚ (fun i : {i : Fin n // i ≠ k} => g i.1) :=
        hg.comp Subtype.val Subtype.val_injective
      have hx' : x ∉ Submodule.span ℚ (Set.range (fun i : {i : Fin n // i ≠ k} => g i.1)) := hx k
      have hp : LinearIndependent ℚ (fun o : Option {i : Fin n // i ≠ k} =>
          Option.casesOn' o x (fun i => g i.1)) :=
        linearIndependent_option'.2 ⟨hk, hx'⟩
      let f : {j : Fin (n + 1) // j ≠ k.succ} → Option {i : Fin n // i ≠ k} := fun j =>
        if h : j.1 = 0 then none
        else some ⟨Fin.pred j.1 h, fun hh => j.2 (by rw [← Fin.succ_pred j.1 h, hh])⟩
      have hf : Function.Injective f := by
        intro j j' hjj
        by_cases hj : j.1 = 0
        · by_cases hj' : j'.1 = 0
          · exact Subtype.ext (by rw [hj, hj'])
          · exfalso
            have h2 : f j = f j' := hjj
            simp only [f, dite_eq_left hj, dite_eq_right hj'] at h2
            exact nomatch h2
        · by_cases hj' : j'.1 = 0
          · exfalso
            have h2 : f j = f j' := hjj
            simp only [f, dite_eq_right hj, dite_eq_left hj'] at h2
            exact nomatch h2
          · have hval : Fin.pred j.1 hj = Fin.pred j'.1 hj' := by
              have h2 : f j = f j' := hjj
              simp only [f, dite_eq_right hj, dite_eq_right hj'] at h2
              exact congrArg Subtype.val (Option.some.inj h2)
            exact Subtype.ext (by
              have h3 := congrArg Fin.succ hval
              rwa [Fin.succ_pred j.1 hj, Fin.succ_pred j'.1 hj'] at h3)
      have hcomp : LinearIndependent ℚ (fun j : {j : Fin (n + 1) // j ≠ k.succ} =>
          Option.casesOn' (f j) x (fun i => g i.1)) :=
        hp.comp f hf
      have hfun : (fun j : {j : Fin (n + 1) // j ≠ k.succ} =>
            Option.casesOn' (f j) x (fun i => g i.1)) =
          (fun j : {j : Fin (n + 1) // j ≠ k.succ} => (@Fin.cons n (fun _ => V) x g) j.1) := by
        funext j
        by_cases hj : j.1 = 0
        · simp only [f, dite_eq_left hj, Option.casesOn'_none]
          rw [hj, Fin.cons_zero]
        · simp only [f, dite_eq_right hj, Option.casesOn'_some]
          conv_rhs => rw [← Fin.succ_pred j.1 hj]
          rw [Fin.cons_succ]
      rw [← hfun]
      exact hcomp

end Work.BW
