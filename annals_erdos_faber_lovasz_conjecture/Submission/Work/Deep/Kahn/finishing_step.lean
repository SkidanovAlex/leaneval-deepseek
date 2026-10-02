import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.Defs
import Submission.Work.Deep.Kahn.FinishSetup
import Submission.Work.Deep.Kahn.FinishAux
import Submission.Work.Deep.Kahn.listProb_facts
import Submission.Work.Deep.Kahn.pair_ratio_bounds
import Submission.Work.Deep.Kahn.one_sub_sum_le_prod
import Submission.Work.Deep.Kahn.listColorable_of_avoids
import Submission.Work.Deep.Prob.LLL.lovaszLocalLemma_asymmetric

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open scoped BigOperators

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

/-- **The finishing step of Kahn's theorem.**

A hypergraph `𝓗` on `Fin n` whose edges have size at most `r`, whose *colour
degrees* `D_x(γ) = #{e ∋ x : γ ∈ L e}` are at most `D`, and whose lists all have
size at least `8 r D` is list-colourable.

The proof is the Lovász local lemma applied to the bad events "the two edges of
the pair `i` receive the same colour" on the product space `ListSpace L` of all
choices of a colour from each list, with the witness `2` times the probability
of the event.  Two distinct meeting edges have the same colour with probability
at most `1/16`, and the sum of these probabilities over the edges meeting a
fixed edge is at most `1/8`; both estimates are proved by double counting the
pairs `(x, γ)` with `x ∈ e` and `γ ∈ L e`
(`Work.Deep.Kahn.pair_ratio_bounds`). -/
theorem finishing_step {n c : ℕ} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    [Fintype 𝓗] (L : 𝓗 → Finset (Fin c)) {r D : ℝ} (hr : 0 < r) (hD : 0 < D)
    (hsize : ∀ e : 𝓗, (ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) : ℝ) ≤ r)
    (hcol : ∀ x : Fin n, ∀ γ : Fin c,
      ((Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} : ℕ) : ℝ) ≤ D)
    (hlist : ∀ e : 𝓗, 8 * r * D ≤ ((L e).card : ℝ)) :
    𝓗.ListColorable L := by
  classical
  -- The lists are nonempty, since `8 r D > 0`.
  have hLne : ∀ e : 𝓗, (L e).Nonempty := by
    intro e
    have hpos : (0 : ℝ) < ((L e).card : ℝ) := lt_of_lt_of_le (by positivity) (hlist e)
    exact Finset.card_pos.mp (by exact_mod_cast hpos)
  -- The two counting estimates.
  obtain ⟨hratio, hsumratio⟩ := pair_ratio_bounds 𝓗 L hr hD hsize hcol hlist
  -- The probability of a bad event is its weight.
  have hprob : ∀ i : BadIdx 𝓗,
      (listProb L hLne).prob (badEvent L i) = badWeight L i := by
    intro i
    have h := (listProb_facts L hLne).2.1 i.1.1 i.1.2 i.2.1
    simpa [badEvent, badWeight] using h
  -- The LLL witnesses lie in `[0,1)`.
  have hx0 : ∀ i : BadIdx 𝓗, 0 ≤ badX L i := by
    intro i
    rw [badX_eq]
    linarith [badWeight_nonneg L i]
  have hx1 : ∀ i : BadIdx 𝓗, badX L i < 1 := by
    intro i
    have h16 : badWeight L i ≤ 1 / 16 := by
      have h := hratio i.1.1 i.1.2 i.2.1 (verts_inter_nonempty_iff i.1.1 i.1.2 |>.mp i.2.2.1)
      simpa [badWeight] using h
    rw [badX_eq]
    linarith
  -- The LLL criterion.
  have hbound : ∀ i : BadIdx 𝓗,
      (listProb L hLne).prob (badEvent L i)
        ≤ badX L i * ∏ j ∈ Dep 𝓗 i, (1 - badX L j) := by
    intro i
    have hsum := sum_badX_Dep_le 𝓗 L hsumratio i
    have hprod : (1 : ℝ) / 2 ≤ ∏ j ∈ Dep 𝓗 i, (1 - badX L j) := by
      have h1 := one_sub_sum_le_prod (Dep 𝓗 i) (badX L)
        (fun j _ => hx0 j) (fun j _ => le_of_lt (hx1 j))
      linarith
    rw [hprob i, badX_eq]
    have hnn := badWeight_nonneg L i
    nlinarith
  -- Independence of an event from the events far from it.
  have hindep : ∀ (i : BadIdx 𝓗) (T : Finset (BadIdx 𝓗)),
      (∀ j ∈ T, j ∉ Dep 𝓗 i ∧ j ≠ i) →
        (listProb L hLne).indepOfCompls (badEvent L i) (badEvent L) T := by
    intro i T hT
    have hmem_bad : ∀ (j : BadIdx 𝓗) (χ : ListSpace L),
        (χ ∈ badEvent L j) ↔ (χ j.1.1).val = (χ j.1.2).val := fun _ _ => Iff.rfl
    have hX : ∀ φ ψ : ListSpace L,
        (∀ c ∈ ({(i).1.1, (i).1.2} : Finset 𝓗), (φ c).val = (ψ c).val) →
        (φ ∈ badEvent L i ↔ ψ ∈ badEvent L i) := by
      intro φ ψ hagree
      rw [hmem_bad i φ, hmem_bad i ψ]
      rw [hagree i.1.1 (by simp), hagree i.1.2 (by simp)]
    have hY : ∀ φ ψ : ListSpace L,
        (∀ c ∉ ({(i).1.1, (i).1.2} : Finset 𝓗), (φ c).val = (ψ c).val) →
        (φ ∈ ⋂ j ∈ T, (badEvent L j)ᶜ ↔ ψ ∈ ⋂ j ∈ T, (badEvent L j)ᶜ) := by
      intro φ ψ hagree
      have hKey : ∀ χ : ListSpace L,
          (χ ∈ ⋂ j ∈ T, (badEvent L j)ᶜ) ↔
            ∀ j ∈ T, (χ j.1.1).val ≠ (χ j.1.2).val := by
        intro χ
        simp only [Set.mem_iInter, Set.mem_compl_iff, hmem_bad]
      rw [hKey φ, hKey ψ]
      constructor
      · intro hh j hj
        have h1 : (φ j.1.1).val = (ψ j.1.1).val :=
          hagree j.1.1 (coords_of_not_mem_Dep (hT j hj).2 (hT j hj).1).1
        have h2 : (φ j.1.2).val = (ψ j.1.2).val :=
          hagree j.1.2 (coords_of_not_mem_Dep (hT j hj).2 (hT j hj).1).2
        intro hcon
        exact hh j hj (h1.trans (hcon.trans h2.symm))
      · intro hh j hj
        have h1 : (φ j.1.1).val = (ψ j.1.1).val :=
          hagree j.1.1 (coords_of_not_mem_Dep (hT j hj).2 (hT j hj).1).1
        have h2 : (φ j.1.2).val = (ψ j.1.2).val :=
          hagree j.1.2 (coords_of_not_mem_Dep (hT j hj).2 (hT j hj).1).2
        intro hcon
        exact hh j hj (h1.symm.trans (hcon.trans h2))
    exact (listProb_facts L hLne).2.2 ({(i).1.1, (i).1.2} : Finset 𝓗) (badEvent L i)
      (⋂ j ∈ T, (badEvent L j)ᶜ) hX hY
  -- The asymmetric Lovász local lemma.
  have hLLL := Work.Deep.Prob.LLL.lovaszLocalLemma_asymmetric (listProb L hLne) (badEvent L) (Dep 𝓗) (badX L)
    hx0 hx1 hbound hindep
  have hprodpos : 0 < ∏ i : BadIdx 𝓗, (1 - badX L i) :=
    Finset.prod_pos fun i _ => by linarith [hx1 i]
  have hpos : 0 < (listProb L hLne).prob (⋂ i, (badEvent L i)ᶜ) :=
    lt_of_lt_of_le hprodpos hLLL
  -- Extract a colouring.
  obtain ⟨φ, hφ⟩ := (listProb L hLne).exists_of_prob_pos hpos
  exact listColorable_of_avoids 𝓗 L φ fun i hi => (Set.mem_iInter.mp hφ i) hi

end Work.Deep.Kahn
