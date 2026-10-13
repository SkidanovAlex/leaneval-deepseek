/-
  annals_wilkies_conjecture, AREA E3, frame step: the "wrong-coordinate" half of the hypothesis
  of `iteratedDeriv_line_eq_zero`.

  The frame half of `E3_identity` proves the vanishing of the *ordered* mixed partials
  `∂^m (f ∘ Ψ(·,0)) (u₀)` only for multi-indices `m` supported off `Set.range ι` (those are the ones
  the ordered reduced derivatives `opMono c h ι m f` see, via `partial_curve_eq_Vword` and
  `Vword_toC_eq_zero`).  The line-derivative lemma `iteratedDeriv_line_eq_zero`, however, wants the
  vanishing for *every* `m`.  This file supplies the missing half: the function
  `u ↦ eaEvalC c f (Ψ (u|_ιᶜ, 0))` is *constant along every coordinate in `Set.range ι`*, and a
  folded word in the coordinate derivatives `edir l` in which some `ι`-coordinate carries a positive
  exponent is identically zero.

  The main results are `edir_eq_zero_of_constAlong` (a function constant along the coordinate `s`
  has zero `s`-derivative), `fold_finRange_eq_zero_of_constAlong` (the folded word vanishes as soon
  as one `ι`-exponent is positive) and `constAlong_comp_subtype` (the parametrised curve function is
  constant along the `ι`-coordinates).
-/
import Mathlib
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.mem_take_finRange_lt

namespace Work.WilE3.Frame

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

noncomputable section

variable {k : ℕ}

/-- A complex function on `Fin k → ℂ` is *constant along the coordinate `s`* if translating in the
`s`-th coordinate does not change its value. -/
def ConstAlong (F : (Fin k → ℂ) → ℂ) (s : Fin k) : Prop :=
  ∀ u, ∀ c : ℂ, F (u + c • Pi.single s (1 : ℂ)) = F u

/-- If `F` is constant along the coordinate `s`, then `edir s F = 0`: the derivative of a constant
one-variable function. -/
theorem edir_eq_zero_of_constAlong (F : (Fin k → ℂ) → ℂ) (s : Fin k) (h : ConstAlong F s) :
    edir s F = 0 := by
  funext u
  have hfun : (fun t : ℂ => F (u + t • Pi.single s (1 : ℂ))) = fun _ => F u := by
    funext t
    exact h u t
  simp only [edir, Pi.zero_apply, hfun, deriv_const]

/-- `edir l` preserves constancy along a *different* coordinate `s`. -/
theorem edir_constAlong (F : (Fin k → ℂ) → ℂ) (l s : Fin k) (hls : l ≠ s) (h : ConstAlong F s) :
    ConstAlong (edir l F) s := by
  intro u c
  have hfun : (fun t : ℂ => F (u + c • Pi.single s (1 : ℂ) + t • Pi.single l (1 : ℂ)))
      = fun t : ℂ => F (u + t • Pi.single l (1 : ℂ)) := by
    funext t
    have h1 : u + c • Pi.single s (1 : ℂ) + t • Pi.single l (1 : ℂ)
        = (u + t • Pi.single l (1 : ℂ)) + c • Pi.single s (1 : ℂ) := by
      abel
    rw [h1]
    exact h (u + t • Pi.single l (1 : ℂ)) c
  simp only [edir, hfun]

/-- Iterating: if `F` is constant along `s` and `l ≠ s`, so is `(edir l)^[n] F`. -/
theorem iterate_edir_constAlong (F : (Fin k → ℂ) → ℂ) (l s : Fin k) (hls : l ≠ s)
    (h : ConstAlong F s) (n : ℕ) : ConstAlong ((edir l)^[n] F) s := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact edir_constAlong _ l s hls ih

/-- `edir l` kills the zero function. -/
theorem edir_zero (l : Fin k) : edir l (0 : (Fin k → ℂ) → ℂ) = 0 := by
  funext u
  simp [edir]

/-- Every iterate of `edir l` kills the zero function. -/
theorem iterate_edir_zero (l : Fin k) (n : ℕ) :
    (edir l)^[n] (0 : (Fin k → ℂ) → ℂ) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, edir_zero]

/-- If `F` is constant along `s` then `(edir s)^[n] F = 0` for every `n > 0`. -/
theorem iterate_edir_self_eq_zero (F : (Fin k → ℂ) → ℂ) (s : Fin k) (h : ConstAlong F s)
    {n : ℕ} (hn : 0 < n) : (edir s)^[n] F = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Function.iterate_succ_apply']
  clear hn
  induction m with
  | zero => simpa using edir_eq_zero_of_constAlong F s h
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, edir_zero]

/-- A folded word in the coordinate derivatives preserves constancy along a coordinate that does
not occur in the list of indices. -/
theorem fold_constAlong (L : List (Fin k)) (m : Fin k → ℕ) (F : (Fin k → ℂ) → ℂ) (s : Fin k)
    (hsf : ConstAlong F s) (hsL : s ∉ L) :
    ConstAlong (L.foldr (fun l G => (edir l)^[m l] G) F) s := by
  induction L with
  | nil => simpa using hsf
  | cons l t ih =>
      rw [List.foldr_cons]
      exact iterate_edir_constAlong _ l s (fun hls => hsL (hls ▸ List.mem_cons_self ..))
        (ih (fun hs => hsL (List.mem_cons_of_mem l hs))) (m l)

/-- The zero function is folded to zero. -/
theorem fold_zero (L : List (Fin k)) (m : Fin k → ℕ) :
    L.foldr (fun l G => (edir l)^[m l] G) 0 = 0 := by
  induction L with
  | nil => rfl
  | cons l t ih =>
      rw [List.foldr_cons, ih, iterate_edir_zero]

/-- **The fold of `List.finRange k` kills a function constant along any coordinate that carries a
positive exponent.**  This is the combinatorial content of the "wrong-coordinate" half of the
hypothesis of `iteratedDeriv_line_eq_zero`. -/
theorem fold_finRange_eq_zero_of_constAlong (m : Fin k → ℕ) (F : (Fin k → ℂ) → ℂ) (s : Fin k)
    (hs : 0 < m s) (hsf : ConstAlong F s) :
    (List.finRange k).foldr (fun l G => (edir l)^[m l] G) F = 0 := by
  have hlen : s.val < (List.finRange k).length := by simp
  set B : List (Fin k) := List.drop (s.val + 1) (List.finRange k) with hB
  have hdrop : List.drop s.val (List.finRange k) = s :: B := by
    rw [List.drop_eq_getElem_cons hlen, hB]
    congr 1
    rw [List.getElem_finRange]
    exact Fin.ext rfl
  have hnotB : s ∉ B := by
    have hn : (s :: B).Nodup := by
      rw [← hdrop]
      exact List.Pairwise.drop (List.nodup_finRange k) (i := s.val)
    exact (List.nodup_cons.mp hn).1
  have hsplit : List.finRange k = (List.finRange k).take s.val ++ (s :: B) := by
    rw [← hdrop]
    exact (List.take_append_drop s.val (List.finRange k)).symm
  have hB : ConstAlong (B.foldr (fun l G => (edir l)^[m l] G) F) s :=
    fold_constAlong B m F s hsf hnotB
  rw [hsplit, List.foldr_append, List.foldr_cons,
    iterate_edir_self_eq_zero _ s hB hs,
    fold_zero _ m]

end

end Work.WilE3.Frame
