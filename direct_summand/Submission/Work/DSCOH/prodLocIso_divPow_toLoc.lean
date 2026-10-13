import Mathlib
import Submission.Work.DSCOH.Basic
import Submission.Work.DSCOH.ProdLocIsoBase

namespace Work.DSCOH

/-- The explicit value of `divPow S k (toLoc S m)` on a fraction: `m/1 ↦ m/X_S^k`. -/
lemma divPow_toLoc_mk_general {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    (S : Finset (Fin n)) (k : ℕ) (m : M) :
    divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m) =
      LocalizedModule.mk m ⟨monomial (A := A) S ^ k,
        Submonoid.pow_mem (subS (A := A) S) (monomial_mem (A := A) S) k⟩ := by
  unfold divPow toLoc
  simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, one_mul]

theorem prodLocIso_divPow_toLoc {A : Type*} [CommRing A] {n : ℕ} {r : ℕ}
    (S : Finset (Fin n)) (k : ℕ) (g : Fin r → Poly A n) :
    prodLocIso (A := A) (n := n) S r
        (divPow (A := A) (n := n) (M := Fin r → Poly A n) S k
          (toLoc (A := A) (n := n) (M := Fin r → Poly A n) S g))
      = fun j => divPow (A := A) (n := n) (M := Poly A n) S k
          (toLoc (A := A) (n := n) (M := Poly A n) S (g j)) := by
  rw [divPow_toLoc_mk_general (A := A) (n := n) (M := Fin r → Poly A n) S k g]
  rw [prodLocIso_mk]
  funext j
  rw [divPow_toLoc_mk_general (A := A) (n := n) (M := Poly A n) S k (g j)]

end Work.DSCOH
