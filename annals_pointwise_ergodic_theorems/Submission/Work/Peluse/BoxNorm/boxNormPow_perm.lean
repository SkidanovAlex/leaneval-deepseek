import Mathlib
import Submission.Work.Peluse.Track.boxSumPow_comp_bij_proved

namespace Work.Peluse.BoxNorm

/-- **The box norm depends on the direction family only up to a permutation of the slots.**  For every
permutation `σ` of `Fin t`, `boxNormPow t (Q ∘ σ) S f = boxNormPow t Q S f`: the cube's corner sum
`Work.Peluse.cornerShift`, the weight `Work.Peluse.weight` and the product over `ω : Fin t → Bool`
are all symmetric under relabelling the `t` slots, so `h ↦ h ∘ σ`, `ω ↦ ω ∘ σ⁻¹` is a bijection of
the summation index sets preserving the cube term (and `∏ i, ((Q (σ i)).card)⁻¹ = ∏ i, ((Q i).card)⁻¹`).

Use: composed with the `Fintype.equivFin` transport it identifies
`Work.Peluse.PETTwo.petDirFam t κ H a` (indexed over `Fin (Fintype.card {ω : Fin t → Bool // ω ≠ 0})`)
with Peluse's Lemma 4.10 direction family `{(c_all − c_ω)[H]}_{ω ≠ all}` of
`Work.Peluse.PetLinear.linear_boxnorm_control_paper` (the complement bijection `ω ↦ ωᶜ` sits
between the two index subtypes, and `Fintype.equivFin` transports it to a permutation of `Fin t`).
This is the missing piece (b) of the reduction
`linear_boxnorm_control_paper + pigeonhole ⟹ PETTwo.pet_family_boxnorm_large_H` recorded in
`NOTES_ucontrol_of_concat_SESSION8.md` §8.

The cube term `∏_ω C^{|ω|} f (x + ω·h + (1-ω)·h')` only sees the index `i` through the pairing of
`Q i` with the `i`-th coordinate of the `x`-shift, so the *complex* box sum is invariant under
relabelling the slots; that statement is already in the tree, in the stronger form needed for the
unnormalised sums, as `Work.Peluse.Track.boxSumPow_comp_bij_proved`
(`boxSumPow t (Q ∘ σ) S f = boxSumPow t Q S f` for any bijection `σ : Fin t → Fin t`).  Since
`boxNormPow` is by definition the modulus `‖boxSumPow t Q S f‖` of that complex number
(`Work.Peluse.BoxNorm.boxNormPow`), the result follows immediately — the same way as in the
wrapper `Work.Peluse.TransferUp.rawPow_comp_bij`.  (The reindexing itself is performed there with
`Equiv.piCongrLeft` on the shift tuples, the invariance of the weight `Work.Peluse.weight` under
`ω ↦ ω ∘ σ` and the invariance `Work.Peluse.cornerShift (α ∘ σ) (β ∘ σ) ω =
cornerShift α β (ω ∘ σ⁻¹)` of the corner sum; the multiplicative factor `∏_i |Q i|²` is permuted
by `Equiv.prod_comp`, which is the `∏ i, ((Q (σ i)).card)⁻¹ = ∏ i, ((Q i).card)⁻¹` of the claim.) -/
theorem boxNormPow_perm {t : ℕ} (σ : Equiv.Perm (Fin t)) (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (f : ℤ → ℂ) :
    Work.Peluse.boxNormPow t (fun i => Q (σ i)) S f = Work.Peluse.boxNormPow t Q S f := by
  have h := Work.Peluse.Track.boxSumPow_comp_bij_proved Q S f (fun i => σ i) σ.bijective
  simpa only [Work.Peluse.boxNormPow] using congrArg (fun z : ℂ => ‖z‖) h

end Work.Peluse.BoxNorm
