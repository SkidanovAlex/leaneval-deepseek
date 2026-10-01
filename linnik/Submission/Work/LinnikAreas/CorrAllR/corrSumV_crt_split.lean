import Mathlib
import Submission.Work.LinnikAreas.CorrAllR.Prelude

open Finset
open scoped BigOperators

namespace Work.LinnikAreas.CorrAllR

open Commons.NumberTheory.DirichletCharacter

/-- The cast of a product in `ZMod n` to `ZMod m` is the product of the casts, for `m ∣ n`. -/
private lemma zmod_cast_prod {n m : ℕ} (h : m ∣ n) {ι : Type*} (s : Finset ι) (f : ι → ZMod n) :
    @ZMod.cast (ZMod m) _ n (∏ i ∈ s, f i) = ∏ i ∈ s, @ZMod.cast (ZMod m) _ n (f i) := by
  rw [← ZMod.castHom_apply (R := ZMod m) (h := h) (∏ i ∈ s, f i),
    map_prod (ZMod.castHom h (ZMod m)) f s]
  exact Finset.prod_congr rfl fun i _ => (ZMod.castHom_apply (R := ZMod m) (h := h) (f i)).symm

/-- The cast of `∏_l (x + g l)` from `ZMod n` to `ZMod m`. -/
private lemma zmod_cast_prod_add {n m : ℕ} (h : m ∣ n) {r : ℕ} (x : ZMod n) (g : Fin r → ℕ) :
    @ZMod.cast (ZMod m) _ n (∏ l : Fin r, (x + (g l : ZMod n)))
      = ∏ l : Fin r, (@ZMod.cast (ZMod m) _ n x + (g l : ZMod m)) := by
  rw [zmod_cast_prod h Finset.univ (fun l : Fin r => x + (g l : ZMod n))]
  exact Finset.prod_congr rfl (fun l _ => by rw [ZMod.cast_add h, ZMod.cast_natCast h])

theorem corrSumV_crt_split {m n : ℕ} [NeZero m] [NeZero n] (hmn : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n)) (r : ℕ) (vv : Fin (r + r) → ℕ) :
    Work.LinnikAreas.corrSumV (m * n) χ r vv
      = Work.LinnikAreas.corrSumV m (Commons.NumberTheory.DirichletCharacter.factorLeft hmn χ) r vv
        * Work.LinnikAreas.corrSumV n (Commons.NumberTheory.DirichletCharacter.factorRight hmn χ) r vv := by
  have key : ∀ x : ZMod (m * n),
      χ (∏ l : Fin r, (x + (vv (Fin.castAdd r l) : ZMod (m * n))))
        * (starRingEnd ℂ) (χ (∏ l : Fin r, (x + (vv (Fin.natAdd r l) : ZMod (m * n)))))
      = (factorLeft hmn χ (∏ l : Fin r, (@ZMod.cast (ZMod m) _ (m * n) x + (vv (Fin.castAdd r l) : ZMod m)))
          * (starRingEnd ℂ)
              (factorLeft hmn χ (∏ l : Fin r, (@ZMod.cast (ZMod m) _ (m * n) x + (vv (Fin.natAdd r l) : ZMod m)))))
        * (factorRight hmn χ (∏ l : Fin r, (@ZMod.cast (ZMod n) _ (m * n) x + (vv (Fin.castAdd r l) : ZMod n)))
          * (starRingEnd ℂ)
              (factorRight hmn χ (∏ l : Fin r, (@ZMod.cast (ZMod n) _ (m * n) x + (vv (Fin.natAdd r l) : ZMod n))))) := by
    intro x
    have hPm := zmod_cast_prod_add (Nat.dvd_mul_right m n) x (fun l => vv (Fin.castAdd r l))
    have hQm := zmod_cast_prod_add (Nat.dvd_mul_right m n) x (fun l => vv (Fin.natAdd r l))
    have hPn := zmod_cast_prod_add (Nat.dvd_mul_left n m) x (fun l => vv (Fin.castAdd r l))
    have hQn := zmod_cast_prod_add (Nat.dvd_mul_left n m) x (fun l => vv (Fin.natAdd r l))
    rw [chi_eq_factors hmn χ (∏ l : Fin r, (x + (vv (Fin.castAdd r l) : ZMod (m * n)))),
      chi_eq_factors hmn χ (∏ l : Fin r, (x + (vv (Fin.natAdd r l) : ZMod (m * n)))),
      map_mul, hPm, hQm, hPn, hQn]
    ring
  have hsum : (∑ x : ZMod (m * n),
        χ (∏ l : Fin r, (x + (vv (Fin.castAdd r l) : ZMod (m * n))))
          * (starRingEnd ℂ) (χ (∏ l : Fin r, (x + (vv (Fin.natAdd r l) : ZMod (m * n))))))
      = (∑ y : ZMod m,
          factorLeft hmn χ (∏ l : Fin r, (y + (vv (Fin.castAdd r l) : ZMod m)))
            * (starRingEnd ℂ)
                (factorLeft hmn χ (∏ l : Fin r, (y + (vv (Fin.natAdd r l) : ZMod m)))))
        * (∑ z : ZMod n,
          factorRight hmn χ (∏ l : Fin r, (z + (vv (Fin.castAdd r l) : ZMod n)))
            * (starRingEnd ℂ)
                (factorRight hmn χ (∏ l : Fin r, (z + (vv (Fin.natAdd r l) : ZMod n))))) := by
    rw [Finset.sum_congr rfl (fun x _ => key x)]
    rw [Fintype.sum_equiv (crtE hmn).toEquiv
      (fun x : ZMod (m * n) =>
        (factorLeft hmn χ (∏ l : Fin r, (@ZMod.cast (ZMod m) _ (m * n) x + (vv (Fin.castAdd r l) : ZMod m)))
          * (starRingEnd ℂ)
              (factorLeft hmn χ (∏ l : Fin r, (@ZMod.cast (ZMod m) _ (m * n) x + (vv (Fin.natAdd r l) : ZMod m)))))
        * (factorRight hmn χ (∏ l : Fin r, (@ZMod.cast (ZMod n) _ (m * n) x + (vv (Fin.castAdd r l) : ZMod n)))
          * (starRingEnd ℂ)
              (factorRight hmn χ (∏ l : Fin r, (@ZMod.cast (ZMod n) _ (m * n) x + (vv (Fin.natAdd r l) : ZMod n))))))
      (fun w : ZMod m × ZMod n =>
        (factorLeft hmn χ (∏ l : Fin r, (w.1 + (vv (Fin.castAdd r l) : ZMod m)))
          * (starRingEnd ℂ)
              (factorLeft hmn χ (∏ l : Fin r, (w.1 + (vv (Fin.natAdd r l) : ZMod m)))))
        * (factorRight hmn χ (∏ l : Fin r, (w.2 + (vv (Fin.castAdd r l) : ZMod n)))
          * (starRingEnd ℂ)
              (factorRight hmn χ (∏ l : Fin r, (w.2 + (vv (Fin.natAdd r l) : ZMod n))))))
      (fun x => by
        have h1 : ((crtE hmn).toEquiv x).1 = @ZMod.cast (ZMod m) _ (m * n) x := crtE_fst hmn x
        have h2 : ((crtE hmn).toEquiv x).2 = @ZMod.cast (ZMod n) _ (m * n) x := crtE_snd hmn x
        rw [h1, h2])]
    rw [Fintype.sum_prod_type]
    exact (Finset.sum_mul_sum Finset.univ Finset.univ
      (fun x : ZMod m =>
        (factorLeft hmn χ (∏ l : Fin r, (x + (vv (Fin.castAdd r l) : ZMod m)))
          * (starRingEnd ℂ)
              (factorLeft hmn χ (∏ l : Fin r, (x + (vv (Fin.natAdd r l) : ZMod m))))))
      (fun y : ZMod n =>
        (factorRight hmn χ (∏ l : Fin r, (y + (vv (Fin.castAdd r l) : ZMod n)))
          * (starRingEnd ℂ)
              (factorRight hmn χ (∏ l : Fin r, (y + (vv (Fin.natAdd r l) : ZMod n))))))).symm
  simp only [corrSumV]
  exact hsum

end Work.LinnikAreas.CorrAllR
