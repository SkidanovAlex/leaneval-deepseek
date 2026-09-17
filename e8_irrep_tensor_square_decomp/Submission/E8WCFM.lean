import Submission.E8WCFW
import Submission.E8ConstChar
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_conj_unique

/-!
# The Weyl character formula for the constituents of the tensor square

`Submission/E8WCFW.lean` proves that the Euler characteristic
`euler Λ = ∑_{N ∈ W} ε(N)·chV(N·Λ)` of the Verma modules on the dot-orbit of a dominant `Λ` is
`W`-invariant.  Together with `euler_top` (value `1` at `Λ`), `euler_support` (support in
`Λ - ℕΦ⁺`) and `euler_freudenthal` (the Freudenthal recursion, valid at every weight), all four
hypotheses of `Submission.E8Character.eq_of_freudenthal` are now available, so `euler Λ` agrees
with the table character `Mnu i` of `Submission/E8Star.lean`.

Consequently the **Weyl character formula for the constituents** holds:

  `A_ρ · Mnu i = A_{Λ i + ρ}`,   i.e.  `∑_{M ∈ W} ε(M)·Mnu i (x - Mρ) = alt (Λ i + ρ) x`.

This is the missing input `(Z)` identified in the earlier sessions; in particular the extraction
of the multiplicities from the Klimyk formula is now available.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

noncomputable section
open scoped BigOperators

namespace Submission.E8WCFM

open Submission.WCFSetup
open Commons.LinearAlgebra.Matrix.Cartan
open Submission.E8Character
open Submission.E8WCFC
open Submission.E8WCFW

/-- **`euler (Λ i) = Mnu i`.** -/
theorem euler_eq_MnuQ (i : Fin 40) :
    (fun v => euler (Submission.E8Extract.ord40get i) v)
      = Submission.E8ConstChar.MnuQ i := by
  funext v
  exact (eq_of_freudenthal (lam := Submission.E8Extract.ord40get i)
    (Submission.E8Star.ord40_dom i)
    (m := Submission.E8ConstChar.MnuQ i)
    (m' := fun v => euler (Submission.E8Extract.ord40get i) v)
    (Submission.E8ConstChar.MnuQ_top i)
    (Submission.E8WCFC.euler_top (Submission.E8Star.ord40_dom i))
    (fun v hv => Submission.E8ConstChar.MnuQ_support i hv)
    (fun v hv => Submission.E8WCFE.euler_support_ht (Submission.E8Star.ord40_dom i) hv)
    (fun v => Submission.E8ConstChar.MnuQ_dc i v)
    (fun v => euler_dc _ (Submission.E8Star.ord40_dom i) v)
    (fun ν hν _ hcon => Submission.E8ConstChar.MnuQ_freud i hν hcon)
    (fun ν _ _ _ => Submission.E8WCFE.euler_freudenthal _ (Submission.E8Star.ord40_dom i) ν) v).symm

/-- **The Weyl character formula for the constituent of highest weight `Λ i`**:
`A_ρ · Mnu i = A_{Λ i + ρ}`. -/
theorem WCF_constituent (i : Fin 40) (x : Fin 8 → ℤ) :
    WSum (Submission.E8ConstChar.MnuQ i) x
      = alt (Submission.E8Extract.ord40get i + rhoV) x := by
  rw [← euler_eq_MnuQ i]
  exact WSum_euler _ x

/-- Two strictly dominant weights conjugate under `W` coincide, and only the identity conjugates
them. -/
theorem ap_eq_of_strict_dominant {M : Matrix (Fin 8) (Fin 8) ℤ} (hM : M ∈ WG)
    {μ ν : Fin 8 → ℤ} (hμ : ∀ i, 1 ≤ μ i) (hν : ∀ i, 1 ≤ ν i) (h : ap M μ = ν) :
    M = 1 ∧ μ = ν := by
  obtain ⟨L, rfl⟩ := mem_WG.mp hM
  have hw : wact L μ = ν := by rwa [wactMat_ap] at h
  have hdomμ : ∀ i, 0 ≤ μ i := fun i => le_trans zero_le_one (hμ i)
  have hdomν : ∀ i, 0 ≤ ν i := fun i => le_trans zero_le_one (hν i)
  have heq : ν = μ := Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_conj_unique hdomν hdomμ
    hw (by rw [Commons.LinearAlgebra.Matrix.Cartan.wact_nil])
  have hfix : wact L μ = μ := by rw [hw, heq]
  have hid := Commons.LinearAlgebra.Matrix.Cartan.E8_wact_fixes_strict_dominant hμ hfix
  refine ⟨?_, heq.symm⟩
  rw [show (1 : Matrix (Fin 8) (Fin 8) ℤ) = wactMat ([] : List (Fin 8)) from wactMat_nil.symm]
  exact wactMat_eq_of_rho_eq (by rw [hid rhoZ, Commons.LinearAlgebra.Matrix.Cartan.wact_nil])

/-- **The value of the alternant at the dominant points.** -/
theorem alt_dominant (i j : Fin 40) :
    alt (Submission.E8Extract.ord40get i + rhoV)
        (Submission.E8Extract.ord40get j + rhoV)
      = if Submission.E8Extract.ord40get i = Submission.E8Extract.ord40get j then 1 else 0 := by
  classical
  have hstrict : ∀ k : Fin 40, ∀ l : Fin 8,
      1 ≤ (Submission.E8Extract.ord40get k + rhoV) l := by
    intro k l
    have h1 := Submission.E8Star.ord40_dom k l
    simp only [Pi.add_apply, rhoV]
    omega
  rw [alt]
  by_cases h : Submission.E8Extract.ord40get i = Submission.E8Extract.ord40get j
  · rw [h]
    rw [Finset.sum_eq_single (1 : Matrix (Fin 8) (Fin 8) ℤ)]
    · simp
    · intro M hM hMne
      rw [if_neg, mul_zero]
      intro hcon
      exact hMne (ap_eq_of_strict_dominant hM (hstrict j) (hstrict j) hcon).1
    · intro h1
      exact absurd WG_one h1
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun M hM => ?_
    rw [if_neg, mul_zero]
    intro hcon
    obtain ⟨-, heq⟩ := ap_eq_of_strict_dominant hM (hstrict i) (hstrict j) hcon
    exact h (add_right_cancel heq)

end Submission.E8WCFM
