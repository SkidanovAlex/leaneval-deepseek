import Mathlib
import Submission.Work.EKLC6Core.atom_iSup_comap_iterate_eq
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces

/-!
# `Work.EKLC6Core.shape_pastSig_eq`

The shape of the atom of the *descending* σ-algebra
`pastSig t M = ⨆ n, (aDiag t ·)^[n] ⁻¹' M` is the set of `u ∈ U` whose conjugates
`aDiag t ^ n * u * (aDiag t ^ n)⁻¹` all lie in the `M`-shape of `x` at the `n`-th point of its
orbit.  It is the elementary bookkeeping lemma behind the transport of the plaque algebra along
the diagonal flow: it combines

* `Work.EKLC6Core.atom_iSup_comap_iterate_eq`, which identifies the atom of `pastSig t M` with the
  set of points whose whole forward orbit meets the corresponding `M`-atoms;
* the action identity `(a ^ n * u * (a ^ n)⁻¹) • (a ^ n • x) = (a ^ n) • (u • x)`;
* the fact that an `A`-normalised subgroup is preserved by conjugation with every power
  `aDiag t ^ n` (`IsHoro`).
-/

open MeasureTheory

set_option warn.classDefReducibility false

namespace Work.EKLC6Core

open Work.EKLContract

/-- **Conjugation by a power of the diagonal flow preserves a horospherical subgroup.**  If `U`
is normalised by every `aDiag s` (`IsHoro`), then it is normalised by every power `aDiag t ^ n`. -/
private lemma conj_pow_mem {U : Subgroup SL3} (hU : IsHoro U) {t : Fin 3 → ℝ} {u : SL3}
    (hu : u ∈ U) (n : ℕ) : aDiag t ^ n * u * (aDiag t ^ n)⁻¹ ∈ U := by
  induction n with
  | zero => simpa using hu
  | succ k ih =>
    rw [pow_succ']
    have key : aDiag t * aDiag t ^ k * u * (aDiag t * aDiag t ^ k)⁻¹
        = aDiag t * (aDiag t ^ k * u * (aDiag t ^ k)⁻¹) * (aDiag t)⁻¹ := by group
    rw [key]
    exact hU.2.1 t _ ih

/-- **The conjugation/iterate identity.**  Applying the `aDiag t ^ n`-conjugate of `u` to the
`n`-th point of the orbit of `x` is the same as applying the `n`-th iterate of the diagonal
action to `u • x`. -/
private lemma orbit_conj_eq (t : Fin 3 → ℝ) (u : SL3) (x : X3) (n : ℕ) :
    (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) • ((fun z : X3 => aDiag t • z)^[n] x)
      = ((fun z : X3 => aDiag t • z)^[n]) (u • x) := by
  calc (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) • ((fun z : X3 => aDiag t • z)^[n] x)
      = (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) • (aDiag t ^ n • x) := by
        rw [smul_iterate_apply]
    _ = ((aDiag t ^ n * u * (aDiag t ^ n)⁻¹) * aDiag t ^ n) • x := by rw [← mul_smul]
    _ = (aDiag t ^ n * u) • x := by
        rw [show (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) * aDiag t ^ n = aDiag t ^ n * u by group]
    _ = aDiag t ^ n • (u • x) := by rw [mul_smul]
    _ = ((fun z : X3 => aDiag t • z)^[n]) (u • x) := by rw [smul_iterate_apply]

theorem shape_pastSig_eq {U : Subgroup Work.EKLContract.SL3} {t : Fin 3 → ℝ}
    {M : MeasurableSpace Work.EKLContract.X3} (hU : Work.EKLContract.IsHoro U) (x : Work.EKLContract.X3) :
    Work.EKLContract.shape (⨆ n : ℕ, MeasurableSpace.comap
        ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) M) U x
      = {u : Work.EKLContract.SL3 | u ∈ U ∧ ∀ n : ℕ,
          Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹
            ∈ Work.EKLContract.shape M U (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x)} := by
  have hatom := atom_iSup_comap_iterate_eq M (fun y : X3 => aDiag t • y) x
  ext u
  constructor
  · intro hu
    rw [shape, Set.mem_ofPred_eq] at hu
    obtain ⟨huU, huMem⟩ := hu
    rw [hatom, Set.mem_ofPred_eq] at huMem
    refine ⟨huU, fun n => ?_⟩
    refine ⟨conj_pow_mem hU huU n, ?_⟩
    rw [orbit_conj_eq]
    exact huMem n
  · rintro ⟨huU, huR⟩
    rw [shape, Set.mem_ofPred_eq]
    refine ⟨huU, ?_⟩
    rw [hatom, Set.mem_ofPred_eq]
    intro n
    have h := (huR n).2
    rw [orbit_conj_eq] at h
    exact h

end Work.EKLC6Core
