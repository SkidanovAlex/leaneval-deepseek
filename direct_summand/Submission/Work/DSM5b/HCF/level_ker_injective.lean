import Mathlib
import Submission.Work.DSM5b.HCF.Complex
import Submission.Work.DSM5b.HCF.surj_cohomology
import Submission.Work.DSM5b.HCF.BlkDefs
import Submission.Work.DSM5b.HCF.blkStepAux
import Submission.Work.DSM5b.HCF.exists_perm_comp_incrBlk

namespace Work.DSM5b.HCF

set_option linter.style.haveILetI false

universe u

open Work.DSM5b

/-- A block element at which the cochain `z` vanishes has `blkVal` zero. -/
lemma blkVal_eq_zero_of_apply {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]
    {ℰ : CoeffSys R ι} {m : ℕ} {S₀ : Finset ι} {z : ℰ.Htc m}
    (σ : BlkIdx S₀ m) (h : z σ.1 = 0) : blkVal ℰ S₀ m z σ = 0 := by
  show ℰ.res (fun x hx => σ.2 ▸ hx) (z σ.1) = 0
  rw [h, map_zero]

/-- **A top-degree cocycle of a coefficient system supported on the subsets of size `k` is
determined by its values on the increasing tuples.**

Let `ℰ` be a coefficient system whose coefficients at the subsets of size `≠ k` vanish (are
subsingletons), and let `z : ℰ.Htc (k-1)` be a cocycle (`ℰ.htcD (k-1) z = 0`) whose restriction
`Work.DSM5b.toStc ℰ (k-1) z` to the increasing tuples is zero.  Then `z = 0`.

Route: pointwise in the tuple.  If `card (tupRng τ) ≠ k` then `z τ` lies in a subsingleton.  If
`card (tupRng τ) = k` then (with `k = k'+1`, so `τ : Fin (k'+1) → ι`) the tuple `τ` is injective
with `k'+1` values in its range `S₀ = tupRng τ`; the block cochain `blkVal ℰ S₀ k' z` is a cocycle
of the surjection complex on `S₀` (`Work.DSM5b.HCF.blkVal_step` gives the "alternating in the
positions" relation for adjacent transpositions), it vanishes at the increasing enumeration
`Work.DSM5b.HCF.incrBlk S₀ k' …` (that tuple *is* increasing, so the hypothesis on `toStc` applies),
and every block element is a permutation of the increasing enumeration
(`Work.DSM5b.HCF.exists_perm_comp_incrBlk`); since adjacent transpositions generate
`Equiv.Perm (Fin (k'+1))` (`Work.DSM5b.HCF.perm_eq_zero_of_step`) the block cochain vanishes
identically, in particular at `τ`. -/
theorem htc_ker_toStc_eq_zero {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]
    [LinearOrder ι] (ℰ : CoeffSys R ι) (k : ℕ)
    (hsub : ∀ S : Finset ι, S.card ≠ k → Subsingleton (ℰ.M S))
    (z : ℰ.Htc (k - 1)) (hz : ℰ.htcD (k - 1) z = 0) (he : toStc ℰ (k - 1) z = 0) :
    z = 0 := by
  rcases k with _ | k'
  · -- `k = 0`: the tuples are singletons, so their range has at least one element.
    funext τ
    have hcard : (tupRng τ).card ≠ 0 := by
      have hmem : τ 0 ∈ tupRng τ := by
        rw [tupRng]
        exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
      have hpos : 0 < (tupRng τ).card := Finset.card_pos.mpr ⟨τ 0, hmem⟩
      omega
    haveI := hsub (tupRng τ) hcard
    exact Subsingleton.elim _ _
  · funext τ
    by_cases hcard : (tupRng τ).card = k' + 1
    · -- the block of `τ`, of size `k'+1`
      let e₀ : BlkIdx (tupRng τ) k' := incrBlk (tupRng τ) k' hcard.symm
      let πBlk : Equiv.Perm (Fin (k' + 1)) → BlkIdx (tupRng τ) k' :=
        fun π => ⟨e₀.1 ∘ ⇑π, (tupRng_comp_perm' π e₀.1).trans e₀.2⟩
      let F : Equiv.Perm (Fin (k' + 1)) → ℰ.M (tupRng τ) :=
        fun π => blkVal ℰ (tupRng τ) k' z (πBlk π)
      have he0 : z e₀.1 = 0 := by
        have h := congrFun he ⟨e₀.1, isIncr_incrBlk (tupRng τ) k' hcard.symm⟩
        simpa using h
      have hF1 : F 1 = 0 := by
        have h1 : πBlk (1 : Equiv.Perm (Fin (k' + 1))) = e₀ := by
          apply Subtype.ext
          show e₀.1 ∘ ⇑(1 : Equiv.Perm (Fin (k' + 1))) = e₀.1
          funext x
          simp
        have hb : blkVal ℰ (tupRng τ) k' z e₀ = 0 := blkVal_eq_zero_of_apply e₀ he0
        exact (congrArg (blkVal ℰ (tupRng τ) k' z) h1).trans hb
      have hstep : ∀ (π : Equiv.Perm (Fin (k' + 1))) (i : Fin k'),
          F (π * Equiv.swap i.castSucc i.succ) = -F π := by
        intro π i
        have h2 : πBlk (π * Equiv.swap i.castSucc i.succ) = swapBlk (πBlk π) i := by
          apply Subtype.ext
          funext x
          simp only [πBlk, swapBlk_val, Equiv.Perm.mul_apply, Function.comp_apply]
        have hb := blkVal_step_fb ℰ k' (tupRng τ) hcard hsub z hz (πBlk π) i
        have hneg : blkVal ℰ (tupRng τ) k' z (swapBlk (πBlk π) i)
            = -blkVal ℰ (tupRng τ) k' z (πBlk π) :=
          eq_neg_of_add_eq_zero_right hb
        exact (congrArg (blkVal ℰ (tupRng τ) k' z) h2).trans hneg
      have hzero : ∀ π, F π = 0 := perm_eq_zero_of_step F hF1 hstep
      obtain ⟨π, hπ⟩ :=
        exists_perm_comp_incrBlk (tupRng τ) hcard.symm (⟨τ, rfl⟩ : BlkIdx (tupRng τ) k')
      have hσ : (⟨τ, rfl⟩ : BlkIdx (tupRng τ) k') = πBlk π := Subtype.ext hπ
      exact (blkVal_self ℰ z τ).symm.trans
        ((congrArg (blkVal ℰ (tupRng τ) k' z) hσ).trans (hzero π))
    · -- the coefficient module at the range of `τ` is a subsingleton
      haveI := hsub (tupRng τ) hcard
      exact Subsingleton.elim _ _

/-- **Injectivity of the comparison map on the top-degree cocycles of the size-`k` graded piece.**
Let `ℰ = Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k` (supported on the subsets of size exactly `k`).
In the top degree `k-1`, a cocycle `z : Htc ℰ (k-1)` (i.e. `htcD z = 0`) is determined by its
restriction `Work.DSM5b.toStc ℰ (k-1) z` to the increasing tuples.

Route: on the block of tuples with `tupRng τ = S₀` (`card S₀ = k`) the complex is the surjection
complex `Work.DSM5b.SurjTerm S₀ (ℰ.M S₀)`/`Work.DSM5b.surjD`, and in the top degree a cocycle there
vanishes at the increasing enumeration iff it is zero (`Work.DSM5b.HCF.surjD_top_kernel_zero` /
`surjD_top_injective`, proved for `S₀ : Finset (Fin n)`; you need the same for `S₀ : Finset ι`
with `[LinearOrder ι]`, e.g. by reindexing along `S₀.orderIsoOfFin` to `Finset.univ : Finset (Fin k)`
or by transcribing the proof).  An increasing tuple of length `k` is exactly the increasing
enumeration of its range, so if `toStc z = 0` then `z` vanishes at every such enumeration, hence on
every block, hence is zero.

Do NOT use `sorry` and do NOT use any frozen `DSMap`/`area_*` declaration. -/
theorem level_ker_injective {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    (𝒜 : Work.DSM5b.CoeffSys R ι) (k : ℕ) :
    Function.Injective (fun z : ↥(LinearMap.ker (Work.DSM5b.CoeffSys.htcD (𝒜 := Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k) (k - 1))) =>
      Work.DSM5b.toStc (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k) (k - 1) z.1) := by
  intro z w hzw
  have hzw' : z - w = 0 := by
    apply Subtype.ext
    show z.1 - w.1 = 0
    refine htc_ker_toStc_eq_zero (CoeffSys.exactlyCoeff 𝒜 k) k
      (fun S hS => exactlyCoeff_subsingleton_of_card_ne 𝒜 k hS) (z.1 - w.1) ?_ ?_
    · rw [map_sub, z.2, w.2, sub_zero]
    · have hzw'' : toStc (CoeffSys.exactlyCoeff 𝒜 k) (k - 1) z.1 =
          toStc (CoeffSys.exactlyCoeff 𝒜 k) (k - 1) w.1 := hzw
      rw [map_sub, hzw'', sub_self]
  exact sub_eq_zero.mp hzw'

end Work.DSM5b.HCF
