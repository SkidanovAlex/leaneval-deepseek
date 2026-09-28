import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.MMVec
import Submission.Work.HP.MMReindex
import Submission.Work.HP.DmixAux.Basic
import Submission.Work.HP.DmixAux.TripleReindex
import Submission.Work.HP.DmixAux.PerA

namespace Work.HP

/-
`D^mix` reindexed as a sum over pairs.
-/
theorem DmixReindex (d n : ℕ) [DecidableEq (Mon d n)] (A B : ℝ) (hB : 1 < B) :
    Dmix d n A B = (Real.log B * (bigW (wOf B) : ℝ) / 4) *
      ∑ᶠ p ∈ Omega d n B,
        Sstar d n 1 (GamMix d n p.1 p.2 (bigW (wOf B))) (TmixSet d n p.2 A (Real.log B)) /
          eNorm (veronese d n p.2) := by
  have hPF : (primSet d n A (fun _ => True)).Finite := primSet_finite d n A (fun _ => True)
  -- the per-`a` identity
  have hPer : ∀ a : Mon d n → ℤ,
      NV d n a B * NVloc d n a B - DeltaMix d n a B
        = (Real.log B * (bigW (wOf B) : ℝ) / 4) *
          ∑ x ∈ (Zx_finite d n a B).toFinset,
            ∑ y ∈ ((Zy_finite d n a B).toFinset).filter (fun y => y ≠ x ∧ y ≠ -x),
              1 / (eNorm a * eNorm (veronese d n y)) :=
    fun a => DmixAux.PerA d n a B hB
  -- `Zx a B ⊆ Xi(B)` and `Zy a B ⊆ Xi(B)`, transported to finsets
  have hZxsub : ∀ a : Mon d n → ℤ, (Zx_finite d n a B).toFinset ⊆ (Xi_finite d n B).toFinset := by
    intro a
    rw [Set.Finite.toFinset_subset]
    intro x hx
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hx.1
  have hZysub : ∀ a : Mon d n → ℤ, (Zy_finite d n a B).toFinset ⊆ (Xi_finite d n B).toFinset := by
    intro a
    rw [Set.Finite.toFinset_subset]
    intro y hy
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hy.1
  -- `Ω(B)` as a finset agrees with the filtered product
  have hOmF : ((Xi_finite d n B).toFinset.product (Xi_finite d n B).toFinset).filter
        (fun p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) => p.1 ≠ p.2 ∧ p.1 ≠ -p.2)
      = (Omega_finite d n B).toFinset := by
    ext p
    simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
      Set.Finite.mem_toFinset, Omega, Set.mem_setOf_eq]
    tauto
  -- the Sstar identity for a single pair
  have hSstar : ∀ p ∈ (Omega_finite d n B).toFinset,
      (∑ a ∈ hPF.toFinset.filter (fun a => p.1 ∈ (Zx_finite d n a B).toFinset ∧
            p.2 ∈ (Zy_finite d n a B).toFinset),
          1 / (eNorm a * eNorm (veronese d n p.2)))
        = Sstar d n 1 (GamMix d n p.1 p.2 (bigW (wOf B))) (TmixSet d n p.2 A (Real.log B)) /
            eNorm (veronese d n p.2) := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    simp only [Omega, Set.mem_setOf_eq] at hp
    obtain ⟨hp1, hp2, -, -⟩ := hp
    have hSfin : {a : Mon d n → ℤ | a ∈ GamMix d n p.1 p.2 (bigW (wOf B)) ∧ IsPrim a ∧
        a ∈ TmixSet d n p.2 A (Real.log B)}.Finite :=
      (finite_of_eNorm_le (ι := Mon d n) A).subset fun a ha => ha.2.2.1
    have hset : hPF.toFinset.filter (fun a => p.1 ∈ (Zx_finite d n a B).toFinset ∧
          p.2 ∈ (Zy_finite d n a B).toFinset) = hSfin.toFinset := by
      ext a
      simp only [Finset.mem_filter]
      rw [Set.Finite.mem_toFinset hPF, Set.Finite.mem_toFinset (Zx_finite d n a B),
        Set.Finite.mem_toFinset (Zy_finite d n a B), Set.Finite.mem_toFinset hSfin]
      simp only [primSet, Set.mem_setOf_eq, Zx, Zy, GamMix, TmixSet, Submodule.mem_inf,
        DmixAux.mem_latOrth_eq_formEval, DmixAux.mem_latMod_eq_formEval, and_true]
      tauto
    rw [hset, Sstar, finsum_mem_eq_finite_toFinset_sum _ hSfin, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pow_one, div_div]
  -- the two constant factors agree and the sums are equal
  have h1 : Dmix d n A B = (Real.log B * (bigW (wOf B) : ℝ) / 4) *
      (∑ a ∈ hPF.toFinset, ∑ x ∈ (Zx_finite d n a B).toFinset,
        ∑ y ∈ ((Zy_finite d n a B).toFinset).filter (fun y => y ≠ x ∧ y ≠ -x),
          1 / (eNorm a * eNorm (veronese d n y))) := by
    rw [Dmix, finsum_mem_eq_finite_toFinset_sum _ hPF, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => hPer a
  have hA : (∑ a ∈ hPF.toFinset, ∑ x ∈ (Zx_finite d n a B).toFinset,
        ∑ y ∈ ((Zy_finite d n a B).toFinset).filter (fun y => y ≠ x ∧ y ≠ -x),
          1 / (eNorm a * eNorm (veronese d n y)))
      = ∑ᶠ p ∈ Omega d n B, Sstar d n 1 (GamMix d n p.1 p.2 (bigW (wOf B)))
          (TmixSet d n p.2 A (Real.log B)) / eNorm (veronese d n p.2) := by
    rw [DmixAux.TripleReindex hPF.toFinset (Xi_finite d n B).toFinset
      (fun a => (Zx_finite d n a B).toFinset) (fun a => (Zy_finite d n a B).toFinset)
      hZxsub hZysub (fun a y => 1 / (eNorm a * eNorm (veronese d n y))), hOmF,
      Finset.sum_congr rfl hSstar,
      finsum_mem_eq_finite_toFinset_sum _ (Omega_finite d n B)]
  rw [h1, hA]

end Work.HP
