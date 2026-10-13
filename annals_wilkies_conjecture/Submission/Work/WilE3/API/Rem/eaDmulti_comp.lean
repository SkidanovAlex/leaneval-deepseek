import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.API.eaD_commute

namespace Work.WilE3.API.Rem

/-!
## Composition of iterated `eaD`'s

`eaDmulti c m Q = ∂_{k-1}^{m (k-1)} ⋯ ∂_0^{m 0} Q` is, by definition of
`WilkiesDesign.E.eaDmulti`, the `List.finRange k`-`foldr` of the iterated operators
`(eaD c i)^[m i]`.  The operators `eaD c i` pairwise commute
(`Work.WilE3.API.eaD_commute`: they are the derivations `∂_{x_i} + ∑_j a_{ji} ψ_j ∂_{ψ_j}`,
whose composing pieces `∂_{x_i}` and `ψ_j ∂_{ψ_j}` all commute), so the block of iterates
with exponents `m'` can be slid to the right of the block with exponents `m`, and the exponents
of matching indices add.

The two abstract list lemmas below do exactly this sliding; the target `eaDmulti_comp` is then
the specialisation `D i = eaD c i`, `L = List.finRange k`.
-/

/-- **Sliding one iterated operator out of a foldr of iterates.**  If the `D i` commute pairwise,
then `(D i)^[a]` may be pulled out of (or pushed into) the composite
`G = fun X => List.foldr (fun j g => (D j)^[n j] g) X L`. -/
theorem foldr_iterate_pull {ι β : Type*} (D : ι → β → β)
    (hcomm : ∀ i j : ι, Function.Commute (D i) (D j)) :
    ∀ (L : List ι) (n : ι → ℕ) (i : ι) (a : ℕ) (X : β),
      (D i)^[a] (List.foldr (fun j g => (D j)^[n j] g) X L) =
        List.foldr (fun j g => (D j)^[n j] g) ((D i)^[a] X) L := by
  intro L
  induction L with
  | nil => intro n i a X; rfl
  | cons j L ih =>
    intro n i a X
    simp only [List.foldr_cons]
    rw [← ih n i a X]
    exact (Function.Commute.iterate_iterate (hcomm i j) a (n j))
      (List.foldr (fun j g => (D j)^[n j] g) X L)

/-- **Composition of two `foldr`s of iterates.**  Applying the composite with exponents `m` to the
composite with exponents `m'` is the composite with exponents `m i + m' i`. -/
theorem foldr_iterate_comp {ι β : Type*} (D : ι → β → β)
    (hcomm : ∀ i j : ι, Function.Commute (D i) (D j)) :
    ∀ (L : List ι) (m m' : ι → ℕ) (Q : β),
      List.foldr (fun i g => (D i)^[m i] g) (List.foldr (fun i g => (D i)^[m' i] g) Q L) L =
        List.foldr (fun i g => (D i)^[(m i) + (m' i)] g) Q L := by
  intro L
  induction L with
  | nil => intro m m' Q; rfl
  | cons j L ih =>
    intro m m' Q
    simp only [List.foldr_cons]
    rw [← foldr_iterate_pull D hcomm L m j (m' j)
      (List.foldr (fun i g => (D i)^[m' i] g) Q L)]
    rw [Function.iterate_add_apply]
    rw [ih m m' Q]

theorem eaDmulti_comp {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (m m' : Fin k → ℕ) (Q : WilkiesDesign.E.EAPoly k r) :
    WilkiesDesign.E.eaDmulti c m (WilkiesDesign.E.eaDmulti c m' Q) = WilkiesDesign.E.eaDmulti c (m + m') Q := by
  simp only [WilkiesDesign.E.eaDmulti]
  exact foldr_iterate_comp (fun i => WilkiesDesign.E.eaD c i)
    (fun i j => Work.WilE3.API.eaD_commute c i j) (List.finRange k) m m' Q

end Work.WilE3.API.Rem
