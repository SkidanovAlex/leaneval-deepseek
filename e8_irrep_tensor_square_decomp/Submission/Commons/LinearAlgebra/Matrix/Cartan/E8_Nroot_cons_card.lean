import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posRoots_finset
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_coords_same_sign

namespace Commons.LinearAlgebra.Matrix.Cartan

/-!
# The number of positive roots sent negative drops by one along a descent

Let `Φ⁺ = E8posRoots.P` be the `120` positive roots of `E₈` and let `w = wact L` be the
Weyl-group element attached to a word `L` of simple reflections.  Write

`N(w) = {y ∈ Φ⁺ : w y ∈ Φ⁻} = E8posRoots.P.filter (fun y => -(wact L y) ∈ E8posRoots.P)`

for the set of positive roots sent to negative roots.

If the simple root `α i` itself lies in `N(w)`, then the element `u = w ∘ sᵢ` — whose word is
`i :: L`, since `wact (i :: L) y = wact L (sref i y)` — has one *fewer* positive root sent to a
negative root, i.e. `|N(u)| + 1 = |N(w)|`.

Mathematically, `sᵢ` sends `αᵢ` to `-αᵢ` and permutes the *other* positive roots among themselves,
so that

`N(w sᵢ) = sᵢ (N(w) \ {αᵢ})`,

an equality of finite sets which gives the cardinality statement through the involution `sᵢ`.
-/

/-- The simple root `αᵢ` of the `E8posRoots` development agrees with the one used by the Weyl
action: both are the `i`-th row of the Cartan matrix. -/
lemma E8_alpha_eq (i : Fin 8) : E8posRoots.alpha i = alpha i :=
  funext fun j => (alpha_apply i j).symm

/-- The simple reflection sends `αᵢ` to `-αᵢ`. -/
lemma E8_sref_alpha (i : Fin 8) : sref i (alpha i) = - alpha i := by
  have h := E8posRoots.sref_alpha i
  rw [E8_alpha_eq i] at h
  exact h

/-- `-αᵢ` is not a positive root. -/
lemma E8_neg_alpha_not_memP (i : Fin 8) : - alpha i ∉ E8posRoots.P := by
  have h := E8posRoots.neg_alpha_not_memP i
  rwa [E8_alpha_eq i] at h

/-- The Weyl action commutes with negation. -/
lemma E8_wact_neg (L : List (Fin 8)) (a : Fin 8 → ℤ) : wact L (-a) = - wact L a := by
  have h := wact_smul L (-1) a
  rw [show (-1 : ℤ) • a = -a from by simp,
      show (-1 : ℤ) • wact L a = - wact L a from by simp] at h
  exact h

/-- A simple reflection preserves positivity of a positive root different from `αᵢ`. -/
lemma E8_sref_mem_P (i : Fin 8) {z : Fin 8 → ℤ} (hz : z ∈ E8posRoots.P) (hne : z ≠ alpha i) :
    sref i z ∈ E8posRoots.P := by
  rw [E8posRoots.memP] at hz ⊢
  exact E8posRoots.sref_mem_posRoot i z hz (fun h => hne (h.trans (E8_alpha_eq i)))

/-- A vector and its negative cannot both be positive roots. -/
lemma E8_neg_not_memP {v : Fin 8 → ℤ} (hv : v ∈ E8posRoots.P) : -v ∉ E8posRoots.P := by
  intro h
  have hv' := (E8posRoots.memP v).mp hv
  have hn' := (E8posRoots.memP (-v)).mp h
  have hzero : ∀ j, E8posRoots.coords v j = 0 := by
    intro j
    have h2 : 0 ≤ E8posRoots.coords v j := hv'.2.2 j
    have h3 : 0 ≤ E8posRoots.coords (-v) j := hn'.2.2 j
    rw [E8posRoots.coords_neg] at h3
    simp only [Pi.neg_apply] at h3
    omega
  have hv0 : v = 0 := by
    have h := E8posRoots.mulVec_coords v
    rw [show E8posRoots.coords v = 0 from funext hzero, Matrix.mulVec_zero] at h
    exact h.symm
  exact hv'.2.1 hv0

/-- **The number of positive roots sent negative drops by one along a descent.**  If the simple root `α i` is itself sent to a negative root by `wact L` (i.e. `α i ∈ N(w)`), then for the element `u = w ∘ sᵢ` (whose word is `i :: L`) the number of positive roots sent to negative roots drops by exactly `1`: `|N(u)| + 1 = |N(w)|`. -/
theorem E8_Nroot_cons_card (L : List (Fin 8)) (i : Fin 8)
    (hi : Commons.LinearAlgebra.Matrix.Cartan.alpha i ∈
      (E8posRoots.P.filter (fun y => -(Commons.LinearAlgebra.Matrix.Cartan.wact L y) ∈ E8posRoots.P))) :
    (E8posRoots.P.filter (fun y => -(Commons.LinearAlgebra.Matrix.Cartan.wact (i :: L) y) ∈ E8posRoots.P)).card + 1
      = (E8posRoots.P.filter (fun y => -(Commons.LinearAlgebra.Matrix.Cartan.wact L y) ∈ E8posRoots.P)).card := by
  classical
  -- unfold the action: `wact (i :: L) = wact L ∘ sᵢ`
  have hfilter : E8posRoots.P.filter (fun y => -(wact (i :: L) y) ∈ E8posRoots.P)
      = E8posRoots.P.filter (fun y => -(wact L (sref i y)) ∈ E8posRoots.P) := rfl
  rw [hfilter]
  -- the hypothesis in `mem_filter` form
  have hiP : alpha i ∈ E8posRoots.P := (Finset.mem_filter.mp hi).1
  have hiN : -(wact L (alpha i)) ∈ E8posRoots.P := (Finset.mem_filter.mp hi).2
  -- the key set identity `N(w sᵢ) = sᵢ (N(w) \ {αᵢ})`
  have hset : E8posRoots.P.filter (fun y => -(wact L (sref i y)) ∈ E8posRoots.P)
      = ((E8posRoots.P.filter (fun y => -(wact L y) ∈ E8posRoots.P)).erase (alpha i)).image (sref i) := by
    ext y
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hyP, hyN⟩
      -- `y ≠ αᵢ`, otherwise `w αᵢ` and `-w αᵢ` are both positive roots
      have hy_ne : y ≠ alpha i := by
        intro hy
        have h1 : wact L (alpha i) ∈ E8posRoots.P := by
          have hs : sref i y = - alpha i := by rw [hy]; exact E8_sref_alpha i
          have := hyN
          rw [hs] at this
          simpa only [E8_wact_neg, neg_neg] using this
        exact E8_neg_not_memP h1 hiN
      -- `sref i y ≠ αᵢ`, else `y = -αᵢ` is not a positive root
      have hsy_ne : sref i y ≠ alpha i := by
        intro hs
        have hy : y = - alpha i := by
          have h2 := congrArg (sref i) hs
          rw [sref_invol, E8_sref_alpha] at h2
          exact h2
        exact E8_neg_alpha_not_memP i (hy ▸ hyP)
      refine ⟨sref i y, ?_, sref_invol i y⟩
      rw [Finset.mem_erase, Finset.mem_filter]
      exact ⟨hsy_ne, E8_sref_mem_P i hyP hy_ne, hyN⟩
    · rintro ⟨z, hz, rfl⟩
      rw [Finset.mem_erase, Finset.mem_filter] at hz
      obtain ⟨hzne, hzP, hzN⟩ := hz
      refine ⟨E8_sref_mem_P i hzP hzne, ?_⟩
      rw [sref_invol]
      exact hzN
  rw [hset, Finset.card_image_of_injective _
        (fun a b hab => by
          have h := congrArg (sref i) hab
          rw [sref_invol i a, sref_invol i b] at h
          exact h), Finset.card_erase_of_mem hi]
  have hpos : 0 < (E8posRoots.P.filter (fun y => -(wact L y) ∈ E8posRoots.P)).card :=
    Finset.card_pos.mpr ⟨alpha i, hi⟩
  omega

end Commons.LinearAlgebra.Matrix.Cartan
