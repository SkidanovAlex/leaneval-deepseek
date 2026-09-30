import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The multiset of images of `Fin.cons a f` over `Finset.univ` is the cons of `a` with the
multiset of images of `f`. -/
theorem univ_val_map_fin_cons {α : Type*} (n : ℕ) (a : α) (f : Fin n → α) :
    (Finset.univ : Finset (Fin (n+1))).val.map (Fin.cons a f)
      = a ::ₘ (Finset.univ : Finset (Fin n)).val.map f := by
  simp only [Finset.val_univ_fin, Multiset.map_coe]
  rw [List.finRange_succ, List.map_cons, ← Multiset.cons_coe, Fin.cons_zero, Multiset.cons_inj_right]
  rw [Multiset.coe_eq_coe]
  have h : (Fin.cons a f ∘ Fin.succ) = f := funext fun i => by simp [Fin.cons_succ]
  rw [List.map_map, h]

/-- **Pair decomposition of an inversion-closed multiset** (with matching multiplicities).  A
multiset of nonzero complex numbers satisfying `R.map (·⁻¹) = R` and containing no self-inverse
element is the disjoint union of `N` chosen elements `w j` (each of modulus `≤ 1`) and their
inverses. -/
theorem pair_decomposition (R : Multiset ℂ) (h0 : ∀ z ∈ R, z ≠ 0)
    (hmult : R.map (fun z => z⁻¹) = R) (hfix : ∀ z ∈ R, z⁻¹ ≠ z) :
    ∃ (N : ℕ) (w : Fin N → ℂ), (∀ j, ‖w j‖ ≤ 1) ∧ R.card = 2 * N ∧
      R = (Finset.univ : Finset (Fin N)).val.map w
            + (Finset.univ : Finset (Fin N)).val.map (fun j => (w j)⁻¹) := by
  classical
  have main : ∀ n, ∀ R : Multiset ℂ, R.card = n → (∀ z ∈ R, z ≠ 0) →
      R.map (fun z => z⁻¹) = R → (∀ z ∈ R, z⁻¹ ≠ z) →
      ∃ (N : ℕ) (w : Fin N → ℂ), (∀ j, ‖w j‖ ≤ 1) ∧ R.card = 2 * N ∧
        R = (Finset.univ : Finset (Fin N)).val.map w
              + (Finset.univ : Finset (Fin N)).val.map (fun j => (w j)⁻¹) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro R hcard h0 hmult hfix
      by_cases hR : R = 0
      · rw [hR]
        exact ⟨0, Fin.elim0, by intro j; exact j.elim0, by simp, by simp⟩
      · obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero hR
        have hz'ne : z⁻¹ ≠ z := hfix z hz
        have hz'mem : z⁻¹ ∈ R := by
          rw [← hmult]
          exact Multiset.mem_map.mpr ⟨z, hz, rfl⟩
        set R2 : Multiset ℂ := (R.erase z).erase z⁻¹ with hR2def
        have h1 : z ::ₘ R.erase z = R := Multiset.cons_erase hz
        have hz'in : z⁻¹ ∈ R.erase z := (Multiset.mem_erase_of_ne hz'ne).mpr hz'mem
        have h2 : z⁻¹ ::ₘ R2 = R.erase z := by
          rw [hR2def]; exact Multiset.cons_erase hz'in
        have hRdecomp : z ::ₘ z⁻¹ ::ₘ R2 = R := by rw [h2]; exact h1
        have hmult2 : R2.map (fun z => z⁻¹) = R2 := by
          have key : (z ::ₘ z⁻¹ ::ₘ R2).map (fun z => z⁻¹) = (z ::ₘ z⁻¹ ::ₘ R2) := by
            rw [hRdecomp, hmult]
          rw [Multiset.map_cons, Multiset.map_cons, inv_inv, Multiset.cons_swap z⁻¹ z,
              Multiset.cons_inj_right, Multiset.cons_inj_right] at key
          exact key
        have h02 : ∀ x ∈ R2, x ≠ 0 := fun x hx =>
          h0 x (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hx))
        have hfix2 : ∀ x ∈ R2, x⁻¹ ≠ x := fun x hx =>
          hfix x (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hx))
        have hcard2 : R.card = R2.card + 2 := by
          rw [← hRdecomp, Multiset.card_cons, Multiset.card_cons]
        have hlt : R2.card < n := by omega
        obtain ⟨N2, w2, hnorm2, hcardR2, hdecomp2⟩ := ih R2.card hlt R2 rfl h02 hmult2 hfix2
        set p : ℂ := if ‖z‖ ≤ 1 then z else z⁻¹ with hpdef
        have hpnorm : ‖p‖ ≤ 1 := by
          rw [hpdef]
          split_ifs with hle
          · exact hle
          · rw [norm_inv]
            exact le_of_lt (inv_lt_one_of_one_lt₀ (lt_of_not_ge hle))
        have hpz : p ::ₘ p⁻¹ ::ₘ ((Finset.univ : Finset (Fin N2)).val.map w2
              + (Finset.univ : Finset (Fin N2)).val.map (fun i => (w2 i)⁻¹))
            = z ::ₘ z⁻¹ ::ₘ ((Finset.univ : Finset (Fin N2)).val.map w2
              + (Finset.univ : Finset (Fin N2)).val.map (fun i => (w2 i)⁻¹)) := by
          rw [hpdef]
          split_ifs with hle
          · rfl
          · rw [inv_inv]
            exact Multiset.cons_swap z⁻¹ z _
        refine ⟨N2 + 1, Fin.cons p w2, ?_, ?_, ?_⟩
        · intro j
          refine Fin.cases ?_ ?_ j
          · simpa [Fin.cons_zero] using hpnorm
          · intro i; simpa [Fin.cons_succ] using hnorm2 i
        · rw [hcard2, hcardR2]; ring
        · rw [← hRdecomp, hdecomp2]
          rw [univ_val_map_fin_cons N2 p w2]
          rw [show (fun j : Fin (N2+1) => ((Fin.cons p w2 : Fin (N2+1) → ℂ) j)⁻¹)
                = (Fin.cons p⁻¹ (fun i => (w2 i)⁻¹) : Fin (N2+1) → ℂ) from by
            funext j
            refine Fin.cases ?_ ?_ j
            · simp [Fin.cons_zero]
            · intro i; simp [Fin.cons_succ]]
          rw [univ_val_map_fin_cons N2 p⁻¹ (fun i => (w2 i)⁻¹)]
          rw [Multiset.cons_add, Multiset.add_cons]
          exact hpz.symm
  exact main R.card R rfl h0 hmult hfix

end Work.BW
