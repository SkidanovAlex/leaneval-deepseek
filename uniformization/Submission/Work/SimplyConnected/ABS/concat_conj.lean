import Mathlib

namespace Work.SimplyConnected.ABS

/-- Telescoping step: a product of two "sandwiches" telescopes at the common factor.

`(A * (C * W⁻¹)) * (W * (B * W'⁻¹))` is homotopic to `A * ((C * B) * W'⁻¹)`.

This is pure `Path.Homotopic` algebra (associativity of `trans`, `symm_trans` and the
identity laws), proved in the homotopy quotient of paths. -/
theorem trans_conj_telescope {X : Type*} [TopologicalSpace X] {y a b c : X} (A : Path y a)
    (C : Path a b) (W : Path y b) (B : Path b c) (W' : Path y c) :
    Path.Homotopic ((A.trans (C.trans W.symm)).trans (W.trans (B.trans W'.symm)))
      (A.trans ((C.trans B).trans W'.symm)) := by
  refine Path.Homotopic.Quotient.eq.mp ?_
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  simp only [Path.Homotopic.Quotient.trans_assoc]
  congr 1
  congr 1
  rw [← Path.Homotopic.Quotient.trans_assoc]
  simp

/-- Concatenating the sandwiches `u k * (v k * (u (k+1))⁻¹)` telescopes to
`u 0 * (v 0 * v 1 * ... * v (n-1)) * (u n)⁻¹`.

This is the general form of `concat_conj`, proved by induction on the number of pieces;
the induction step appends one more sandwich on the right and uses `trans_conj_telescope`. -/
theorem concat_conj_aux {X : Type*} [TopologicalSpace X] :
    ∀ (n : ℕ) (y : X) (p : Fin (n + 1) → X)
    (u : (i : Fin (n + 1)) → Path y (p i))
    (v : (k : Fin n) → Path (p k.castSucc) (p k.succ)),
    Path.Homotopic
      (Path.concat (fun _ : Fin (n + 1) => y)
        (fun k : Fin n => (u k.castSucc).trans ((v k).trans (u k.succ).symm)))
      ((u 0).trans ((Path.concat p v).trans (u (Fin.last n)).symm)) := by
  intro n
  induction n with
  | zero =>
    intro y p u v
    rw [Path.concat_zero, Path.concat_zero]
    exact Path.Homotopic.symm (Path.Homotopic.trans
      (Path.Homotopic.hcomp (Path.Homotopic.refl _) (Path.Homotopic.refl_trans _))
      (Path.Homotopic.trans_symm _))
  | succ n ih =>
    intro y p u v
    rw [Path.concat_succ (fun _ : Fin (n + 2) => y)
      (fun k : Fin (n + 1) => (u k.castSucc).trans ((v k).trans (u k.succ).symm))]
    have hIH := ih y (fun i => p (Fin.castSucc i)) (fun i => u (Fin.castSucc i))
      (fun k => v (Fin.castSucc k))
    rw [Path.concat_succ p v]
    refine Path.Homotopic.trans (Path.Homotopic.hcomp hIH (Path.Homotopic.refl _)) ?_
    exact trans_conj_telescope _ _ _ _ _

theorem concat_conj {X : Type*} [TopologicalSpace X] (n : ℕ) (x : X)
    (xs : Fin (n + 1) → X) (gs : (i : Fin (n + 1)) → Path x (xs i))
    (cs : (k : Fin n) → Path (xs k.castSucc) (xs k.succ)) :
    Path.Homotopic
      (Path.concat (fun _ : Fin (n + 1) => x)
        (fun k : Fin n => (gs k.castSucc).trans ((cs k).trans (gs k.succ).symm)))
      ((gs 0).trans ((Path.concat xs cs).trans (gs (Fin.last n)).symm)) := by
  exact concat_conj_aux n x xs gs cs

end Work.SimplyConnected.ABS
