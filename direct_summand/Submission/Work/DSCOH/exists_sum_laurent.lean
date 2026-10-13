import Mathlib
import Submission.Work.DSCOH.ShiftToolkit
import Submission.Work.DSCOH.divPow_toLoc_eq_sum_laurent
import Submission.Work.DSCOH.sum_coord_sub
import Submission.Work.DSCOH.fiber_sum

namespace Work.DSCOH

open MvPolynomial

/-- Every element of `degZero (shift d) univ` is `m / X_univ^k` for a *single* polynomial
`m ∈ shift d (k·n)`.  The pieces `shift d (k·n) / X_univ^k` are increasing in `k` (because
multiplication by `X_univ` shifts the grading by `n`), so the `⨆` defining `degZero` is a
directed union and a single index suffices. -/
theorem exists_gen_of_mem_degZero_shift {A : Type*} [CommRing A] {n : ℕ} (d : ℕ)
    {z : locAt (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n))}
    (hz : z ∈ degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d)
      (Finset.univ : Finset (Fin n))) :
    ∃ (k : ℕ) (m : Poly A n), m ∈ shift (A := A) (n := n) d (k * n) ∧
      divPow (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n)) k
        (toLoc (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n)) m) = z := by
  have hz' : z ∈ ⨆ k : ℕ, Submodule.map
      ((divPow (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n)) k).comp
        (toLoc (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n))))
      (shift (A := A) (n := n) d (k * (Finset.univ : Finset (Fin n)).card)) := hz
  rw [Finset.card_univ, Fintype.card_fin] at hz'
  have hmono : Monotone (fun k : ℕ => Submodule.map
      ((divPow (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n)) k).comp
        (toLoc (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n))))
      (shift (A := A) (n := n) d (k * n))) := by
    apply monotone_nat_of_le_succ
    intro k
    rintro _ ⟨m, hm, rfl⟩
    refine Submodule.mem_map.mpr
      ⟨(monomial (A := A) (Finset.univ : Finset (Fin n))) ^ 1 • m, ?_, ?_⟩
    · rw [pow_one]
      have hmem : xpow (A := A) (n := n) (fun _ : Fin n => (1:ℕ)) ∈ homSub A n n := by
        have h := xpow_mem_homSub (A := A) (n := n) (fun _ : Fin n => (1:ℕ))
        rwa [show (∑ i : Fin n, (1:ℕ)) = n from by simp] at h
      rw [xpow_one] at hmem
      have hsm := (shift_gradedSMul (A := A) (n := n) d).smul_mem hmem hm
      rwa [show n +ᵥ (k * n) = (k + 1) * n from by rw [vadd_eq_add]; ring] at hsm
    · exact divPow_toLoc_smul_monomial_pow (A := A) (n := n)
        (Finset.univ : Finset (Fin n)) k 1 m
  obtain ⟨k, m, hm, hkm⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hz'
  exact ⟨k, m, hm, hkm⟩

theorem exists_sum_laurent {A : Type*} [CommRing A] {n : ℕ} (d : ℕ)
    {z : locAt (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n))}
    (hz : z ∈ degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d)
      (Finset.univ : Finset (Fin n))) :
    ∃ (F : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → A),
      (∀ β ∈ F, (∑ i, β i) = -(d : ℤ)) ∧ z = ∑ β ∈ F, c β • laurent (A := A) (n := n) β := by
  classical
  obtain ⟨k, m, hm, hkm⟩ := exists_gen_of_mem_degZero_shift (A := A) (n := n) d hz
  let ψ : (Fin n →₀ ℕ) → (Fin n → ℤ) := fun v i => (v i : ℤ) - (k : ℤ)
  have hψinj : Function.Injective ψ := by
    intro v w hvw
    ext i
    have h := congrFun hvw i
    simp only [ψ] at h
    have : (v i : ℤ) = (w i : ℤ) := by linarith
    exact_mod_cast this
  refine ⟨m.support.image ψ,
    fun β => ∑ v ∈ m.support.filter (fun v => ψ v = β), m.coeff v, ?_, ?_⟩
  · intro β hβ
    rw [Finset.mem_image] at hβ
    obtain ⟨v, hv, rfl⟩ := hβ
    exact sum_coord_sub (A := A) (n := n) (d := d) (k := k) hm hv
  · have hC := divPow_toLoc_eq_sum_laurent (A := A) (n := n) (k := k) (m := m)
    have hD := fiber_sum (A := A) (n := n) (s := m.support) (ψ := ψ)
      (fun a _ b _ h => hψinj h) (fun v => m.coeff v) (fun β => laurent (A := A) (n := n) β)
    rw [← hkm, hC, ← hD]

end Work.DSCOH
