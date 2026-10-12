import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The symmetrisation average is permutation invariant

`symAvgAmb N p = (N!)⁻¹ • ∑_σ permAmb N σ p` is the average of the permutation
orbit of `p` in the ambient space `Amb N`.  It is invariant under every particle
permutation, `IsSym N (symAvgAmb N p)`.

The proof is the standard group-average argument, and rests on the fact that
`permAmb` is a `ℝ`-linear action of the symmetric group on `Amb N`:

* `permAmb N σ` is additive (`permAmb_add`) and compatible with scalars
  (`permAmb_smul`), hence distributes over the finite sum defining the average
  (`permAmb_sum`);
* `permAmb` is multiplicative, `permAmb N σ (permAmb N τ p) = permAmb N (σ * τ) p`
  (`permAmb_mul`), which is checked componentwise and reduces to
  `permLp N σ (permLp N τ u) = permLp N (σ * τ) u` (`permLp_mul`).

Then `permAmb N σ (symAvgAmb N p) = (N!)⁻¹ • ∑_τ permAmb N σ (permAmb N τ p)
= (N!)⁻¹ • ∑_τ permAmb N (σ * τ) p = (N!)⁻¹ • ∑_τ permAmb N τ p`, the last step
reindexing the sum along the bijection `τ ↦ σ * τ` of the symmetric group.
-/

namespace Work.BoseSym.Perm

open MeasureTheory

/-! ## Composition of the permutation actions -/

/-- The permutation action on configuration space is a contravariant action:
`tauPerm τ ∘ tauPerm σ = tauPerm (σ * τ)`. -/
private lemma tauPerm_comp {N : ℕ} (σ τ : Equiv.Perm (Fin N)) :
    tauPerm N τ ∘ tauPerm N σ = tauPerm N (σ * τ) := by
  funext x i
  simp [tauPerm, Equiv.Perm.mul_apply]

/-- `permLp` is multiplicative: composing the `L²` actions of `σ` and `τ` gives
the action of `σ * τ`. -/
private lemma permLp_mul {N : ℕ} (σ τ : Equiv.Perm (Fin N)) (u : L2 N) :
    permLp N σ (permLp N τ u) = permLp N (σ * τ) u := by
  show Lp.compMeasurePreserving (tauPerm N σ) (measurePreserving_tauPerm N σ)
    (Lp.compMeasurePreserving (tauPerm N τ) (measurePreserving_tauPerm N τ) u) = _
  rw [(Lp.compMeasurePreserving_comp_apply u (measurePreserving_tauPerm N τ)
    (measurePreserving_tauPerm N σ)).symm]
  simp only [tauPerm_comp]
  rfl

/-- `permLp` is compatible with scalar multiplication. -/
private lemma permLp_smul {N : ℕ} (σ : Equiv.Perm (Fin N)) (c : ℝ) (u : L2 N) :
    permLp N σ (c • u) = c • permLp N σ u := by
  show Lp.compMeasurePreservingₗ ℝ (tauPerm N σ) (measurePreserving_tauPerm N σ) (c • u)
     = c • Lp.compMeasurePreservingₗ ℝ (tauPerm N σ) (measurePreserving_tauPerm N σ) u
  exact map_smul _ _ _

/-! ## `permAmb` as an additive action -/

private lemma permAmb_zero {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    permAmb N σ (0 : Amb N) = 0 := by
  apply Prod.ext
  · simp only [permAmb_fst, Prod.fst_zero, map_zero]
  · funext j
    simp only [permAmb_snd, Prod.snd_zero, Pi.zero_apply, map_zero]

private lemma permAmb_add {N : ℕ} (σ : Equiv.Perm (Fin N)) (p q : Amb N) :
    permAmb N σ (p + q) = permAmb N σ p + permAmb N σ q := by
  apply Prod.ext
  · simp only [permAmb_fst, Prod.fst_add, map_add]
  · funext j
    simp only [permAmb_snd, Pi.add_apply, Prod.snd_add, map_add]

private lemma permAmb_smul {N : ℕ} (σ : Equiv.Perm (Fin N)) (c : ℝ) (p : Amb N) :
    permAmb N σ (c • p) = c • permAmb N σ p := by
  apply Prod.ext
  · simp only [permAmb_fst, Prod.smul_fst, permLp_smul]
  · funext j
    simp only [permAmb_snd, Prod.smul_snd, Pi.smul_apply, permLp_smul]

/-- `permAmb` is multiplicative, so that it is an action of the symmetric group
on the ambient space. -/
private lemma permAmb_mul {N : ℕ} (σ τ : Equiv.Perm (Fin N)) (p : Amb N) :
    permAmb N σ (permAmb N τ p) = permAmb N (σ * τ) p := by
  apply Prod.ext
  · simp only [permAmb_fst, permLp_mul]
  · funext j
    simp only [permAmb_snd, permLp_mul]
    congr 1

/-- `permAmb N σ` distributes over finite sums. -/
private lemma permAmb_sum {N : ℕ} (σ : Equiv.Perm (Fin N)) {ι : Type*} (s : Finset ι)
    (f : ι → Amb N) :
    permAmb N σ (∑ i ∈ s, f i) = ∑ i ∈ s, permAmb N σ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [permAmb_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, permAmb_add, ih]

/-! ## The symmetrisation average is invariant -/

theorem symAvgAmb_isSym {N : ℕ} (p : Amb N) : IsSym N (symAvgAmb N p) := by
  intro σ
  have hs : permAmb N σ (∑ τ : Equiv.Perm (Fin N), permAmb N τ p)
      = ∑ τ : Equiv.Perm (Fin N), permAmb N σ (permAmb N τ p) :=
    permAmb_sum σ Finset.univ (fun τ => permAmb N τ p)
  have hσ : (∑ τ : Equiv.Perm (Fin N), permAmb N (σ * τ) p)
      = ∑ τ : Equiv.Perm (Fin N), permAmb N τ p :=
    Equiv.sum_comp (Equiv.mulLeft σ) (fun τ => permAmb N τ p)
  rw [symAvgAmb, permAmb_smul, hs]
  simp only [permAmb_mul]
  rw [hσ]

end Work.BoseSym.Perm
