/-
  WilE8 — the four deliverables of area E8.

  `E8_reduce_proved` and `E8_comps_proved` are in `Assemble.lean`; here we build the
  `SOMin` structure (`genSOMin`, level `Ω = Gen`) with `comps` from `E8_comps_proved`, and
  prove `E8_sharpCD` (E8c) and `E8_boxZero` (E8d) for it.

  All four theorems take the *verbatim* frozen statements of the area-E7 holes
  (`E7_star_compl`, `E7_star_inter`, `E7_bv_main`) and of the area-E2 hole (`E2_components`)
  as explicit leading hypotheses.  The conclusions are the frozen conclusions:
  `genSOMin.SharpCD` and `boxZero M P ∈ genSOMin.Ω F D N`, with `genSOMin.Ω = Gen` (this file's
  structure term is definitionally the frozen `genSOMin` up to its `comps` component, which is
  filled here by the *proved* `E8_comps_proved` instead of the frozen `sorry`).
-/
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE8.Assemble
import Submission.Work.WilE8.Box.boxZero_starR
import Submission.Work.WilE8.Sharp.sharpCD_starR
import Submission.Work.WilE8.Poly.poly_bound

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology
namespace Work.WilE8
open WilkiesDesign WilkiesDesign.E

/-- The sharply o-minimal structure of area E: the smallest family `Gen` closed under the
`SOMin` axioms and containing the transported `*`-sets, with `comps` supplied by
`E8_comps_proved`.  This is the frozen `WilkiesDesign.E.genSOMin` with its `comps` field
replaced by a proved one. -/
noncomputable def genSOMin
    (hCompl : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (Y : Set (Fin n → ℝ)),
      Star F D n Y → Star a (p.eval D) n (cubeC n \ Y))
    (hInter : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (k : ℕ) (D : Fin k → ℕ)
      (Y : Fin k → Set (Fin n → ℝ)), (∀ i, Star F (D i) n (Y i)) →
      Star a (p.eval (∑ i, D i)) n (cubeC n ∩ ⋂ i, Y i))
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y) :
    SOMin where
  Ω := Gen
  mono_F := fun h => Gen.mono_F h
  mono_D := fun h => Gen.mono_D h
  compl := fun h => Gen.compl h
  proj := fun h => Gen.proj h
  prod_right := fun h => Gen.prod_right h
  prod_left := fun h => Gen.prod_left h
  union := fun D A h => Gen.union D A h
  inter := fun D A h => Gen.inter D A h
  hyp := fun n P => Gen.hyp n P
  comps := fun F => E8_comps_proved hCompl hInter hE2 F

/-- **E8d.** The truncated exp-polynomial zero sets; format and degree do not depend on `M`. -/
theorem E8_boxZero_proved
    (hCompl : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (Y : Set (Fin n → ℝ)),
      Star F D n Y → Star a (p.eval D) n (cubeC n \ Y))
    (hInter : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (k : ℕ) (D : Fin k → ℕ)
      (Y : Fin k → Set (Fin n → ℝ)), (∀ i, Star F (D i) n (Y i)) →
      Star a (p.eval (∑ i, D i)) n (cubeC n ∩ ⋂ i, Y i))
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y) :
    ∀ N d : ℕ, ∃ F D : ℕ, ∀ (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ),
      P.totalDegree ≤ d → boxZero M P ∈ (genSOMin hCompl hInter hE2).Ω F D N := by
  intro N d
  obtain ⟨F, D, h⟩ := Box.boxZero_starR hE2 N d
  exact ⟨F, D, fun M P hP => Gen.star (h M P hP)⟩

/-- **E8c.** Sharp cell decomposition, from `E7_bv_main` on the cube and the transport by
`psiV`. -/
theorem E8_sharpCD_proved
    (hCompl : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (Y : Set (Fin n → ℝ)),
      Star F D n Y → Star a (p.eval D) n (cubeC n \ Y))
    (hInter : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (k : ℕ) (D : Fin k → ℕ)
      (Y : Fin k → Set (Fin n → ℝ)), (∀ i, Star F (D i) n (Y i)) →
      Star a (p.eval (∑ i, D i)) n (cubeC n ∩ ⋂ i, Y i))
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hBV : ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D k : ℕ) (Y : Fin k → Set (Fin n → ℝ)), (∀ i, Star F D n (Y i)) →
      ∃ C : Finset (Set (Fin n → ℝ)), IsCylDecompOn n (cubeC n) C ∧
        (∀ i, ∀ κ ∈ C, κ ⊆ Y i ∨ Disjoint κ (Y i)) ∧
        C.card ≤ MvPolynomial.eval ![D, k] b ∧ ∀ κ ∈ C, Star a (c.eval D) n κ) :
    (genSOMin hCompl hInter hE2).SharpCD := by
  intro F n
  obtain ⟨a0, P0, -, hRed⟩ := E8_reduce_proved hCompl hInter hE2 F n
  obtain ⟨a, b, c, hCD⟩ := Sharp.sharpCD_starR hBV hInter ocube_star' a0 n
  obtain ⟨b', hb'⟩ := Poly.poly_bound P0 b
  refine ⟨a, b', c.comp P0, fun D k X hX => ?_⟩
  obtain ⟨C, hC1, hC2, hC3, hC4⟩ := hCD (P0.eval D) k X (fun i => hRed D (X i) (hX i))
  refine ⟨C, hC1, hC2, ?_, ?_⟩
  · rw [hb' D k]; exact hC3
  · intro κ hκ
    refine Gen.star (StarR.mono (hC4 κ hκ) le_rfl ?_)
    exact le_of_eq (by rw [Polynomial.eval_comp])

end Work.WilE8
