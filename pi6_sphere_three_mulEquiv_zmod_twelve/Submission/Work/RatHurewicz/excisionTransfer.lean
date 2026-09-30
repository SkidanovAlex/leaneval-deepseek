import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.excisionDefs
import Submission.Work.StemsB.PiMap

/-!
# Compression implies isomorphisms on homotopy groups

The compression property of a pair `(X, A)` (tom Dieck, *Algebraic Topology*, (6.7.5)(1)) in
dimensions `≤ n` is equivalent to: the inclusion `A ↪ X` induces bijections
`π_{j}(A,a₀) → π_{j}(X,a₀)` for `j ≤ n - 1`.  This file proves the easy implication
(compression ⟹ isomorphism), which is the last step of the proof of
`Work.RatHurewicz.excisionRelPiVanishing`: Puppe's argument produces the compression of the pair
`(F, range ι)` of homotopy fibres in dimensions `≤ p + q + 1`, and this lemma converts it into the
bijectivity of `πmap ι` in the range.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz

open Work.StemsB

noncomputable section

/-- **Compression in dimensions `≤ n` implies that the inclusion induces isomorphisms of homotopy
groups in degrees `≤ n - 1`.**

If every map of pairs `(I^d, ∂I^d) → (X, A)` with `d ≤ n` is homotopic relative to `∂I^d` into `A`,
then for every `j` with `j + 2 ≤ n` the map `π_{j+1}(A, a₀) → π_{j+1}(X, a₀)` induced by the
inclusion is bijective.

The two directions are the classical ones: surjectivity compresses a based cube of `X` into `A`
(and re-reads it as a based cube of `A`), injectivity compresses a based homotopy between the
images of two based cubes of `A` (a based `(j+2)`-cube of `X` with boundary in `A`) into `A`. -/
theorem bijective_πmap_setIncl_of_compressRel {X : Type} [TopologicalSpace X] {A : Set X}
    (a₀ : ↥A) (n : ℕ) (h : ∀ d, d ≤ n → CompressRel X A d) :
    ∀ j, j + 2 ≤ n → Function.Bijective (πmap (setIncl A) j a₀) := by
  intro j hj
  have hj1 : j + 1 ≤ n := by omega
  constructor
  · -- injectivity
    intro a b hab
    induction a using Quotient.inductionOn with
    | h p =>
      induction b using Quotient.inductionOn with
      | h q =>
        rw [πmap_apply_mk, πmap_apply_mk] at hab
        have hhop : GenLoop.Homotopic (genLoopMap (setIncl A) (j + 1) p)
            (genLoopMap (setIncl A) (j + 1) q) := Quotient.exact hab
        obtain ⟨H⟩ := hhop
        have hH'bd : ∀ x, x ∈ Cube.boundary (Fin (j + 2)) → H (x 0, Fin.tail x) ∈ A := by
          intro x hx
          obtain ⟨i, hi⟩ := hx
          rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨k, hk⟩
          · subst h0
            rcases hi with h | h
            · rw [show (x 0 : I) = 0 from h, H.apply_zero (Fin.tail x)]
              exact (p (Fin.tail x)).2
            · rw [show (x 0 : I) = 1 from h, H.apply_one (Fin.tail x)]
              exact (q (Fin.tail x)).2
          · subst hk
            have htail : Fin.tail x ∈ Cube.boundary (Fin (j + 1)) :=
              ⟨k, by rw [show Fin.tail x k = x k.succ from rfl]; exact hi⟩
            have hprop : H (x 0, Fin.tail x) = (setIncl A) (p (Fin.tail x)) := by
              have hh := (H.prop' (x 0)) (Fin.tail x) htail
              simpa [ContinuousMap.Homotopy.curry_apply, ContinuousMap.HomotopyWith.coe_toHomotopy] using hh
            rw [hprop]
            exact (p (Fin.tail x)).2
        let H' : C(ICube (j + 2), X) := ⟨fun x => H (x 0, Fin.tail x), by fun_prop⟩
        obtain ⟨K, hK0, hKb, hK1⟩ := h (j + 2) hj H' hH'bd
        refine Quotient.sound ⟨{ toHomotopy := { toFun := fun z => ⟨K (Fin.cons z.1 z.2, 1), hK1 _⟩, continuous_toFun := ?_, map_zero_left := ?_, map_one_left := ?_ }, prop' := ?_ }⟩
        · refine Continuous.subtype_mk ?_ _
          exact K.continuous.comp (by fun_prop)
        · intro y
          apply Subtype.ext
          show K (Fin.cons 0 y, 1) = (p y : X)
          rw [hKb (Fin.cons 0 y) ⟨0, Or.inl rfl⟩ 1]
          show H ((Fin.cons (0:I) y : Fin (j+2) → I) 0, Fin.tail (Fin.cons (0:I) y : Fin (j+2) → I)) = (p y : X)
          rw [Fin.cons_zero, Fin.tail_cons, H.apply_zero y]
          rfl
        · intro y
          apply Subtype.ext
          show K (Fin.cons 1 y, 1) = (q y : X)
          rw [hKb (Fin.cons 1 y) ⟨0, Or.inr rfl⟩ 1]
          show H ((Fin.cons (1:I) y : Fin (j+2) → I) 0, Fin.tail (Fin.cons (1:I) y : Fin (j+2) → I)) = (q y : X)
          rw [Fin.cons_zero, Fin.tail_cons, H.apply_one y]
          rfl
        · intro t y hy
          apply Subtype.ext
          show K (Fin.cons t y, 1) = (p y : X)
          obtain ⟨k, hk⟩ := hy
          rw [hKb (Fin.cons t y) ⟨k.succ, by rw [Fin.cons_succ]; exact hk⟩ 1]
          show H.toFun ((Fin.cons t y : Fin (j+2) → I) 0, Fin.tail (Fin.cons t y : Fin (j+2) → I)) = (p y : X)
          rw [Fin.cons_zero, Fin.tail_cons]
          show H.toFun (t, y) = (p y : X)
          have hh := (H.prop' t) y (⟨k, hk⟩ : y ∈ Cube.boundary (Fin (j + 1)))
          simpa [setIncl] using hh
  · -- surjectivity
    intro y
    induction y using Quotient.inductionOn with
    | h f =>
      have hbdf : ∀ x, x ∈ Cube.boundary (Fin (j + 1)) → f.1 x ∈ A := by
        intro x hx
        rw [f.2 x hx]
        exact a₀.2
      obtain ⟨G, hG0, hGb, hG1⟩ := h (j + 1) hj1 f.1 hbdf
      let g : Ω^ (Fin (j + 1)) ↥A a₀ :=
        ⟨⟨fun x => ⟨G (x, 1), hG1 x⟩, by fun_prop⟩, by
          intro x hx
          apply Subtype.ext
          show G (x, 1) = (a₀ : X)
          rw [hGb x hx 1]
          exact f.2 x hx⟩
      refine ⟨⟦g⟧, ?_⟩
      rw [πmap_apply_mk]
      apply Quotient.sound
      have hhom : (f.1).HomotopicRel ((genLoopMap (setIncl A) (j + 1) g).1) (Cube.boundary (Fin (j + 1))) := by
        refine ⟨{ toHomotopy := { toFun := fun p => G (p.2, p.1), continuous_toFun := ?_, map_zero_left := ?_, map_one_left := ?_ }, prop' := ?_ }⟩
        · exact G.continuous.comp (continuous_snd.prodMk continuous_fst)
        · intro x
          show G (x, 0) = f.1 x
          exact hG0 x
        · intro x
          show G (x, 1) = (setIncl A) (g x)
          rfl
        · intro t x hx
          show G (x, t) = f.1 x
          exact hGb x hx t
      exact hhom.symm

end

end Work.RatHurewicz
