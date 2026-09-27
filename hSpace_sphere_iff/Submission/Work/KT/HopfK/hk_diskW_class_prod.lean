import Mathlib
import Submission.Work.KT.HopfK.Disk

namespace Work.KT.HopfK

/-- Bilinearity of the product on differences. -/
private lemma prod_sub_sub {A : Type} [CommRing A] (μ : K0 A →+ K0 A →+ K0 A) (x y z w : K0 A) :
    μ (x - y) (z - w) = (μ x z - μ x w) - (μ y z - μ y w) := by
  rw [map_sub, map_sub]
  simp only [AddMonoidHom.sub_apply]
  abel

/-- The class of `Q₁ = P ⊗ Q ⊕ E ⊗ E`. -/
private lemma cls_diskQ1 {A : Type} [CommRing A] (n : ℕ)
    (P Q E : Matrix (Fin n) (Fin n) A) (hP : P * P = P) (hQ : Q * Q = Q) (hE : E * E = E) :
    cls (⟨n * n + n * n, diskQ1 P Q E⟩ : Mat A)
      = cls (Mat.kron (⟨n, P⟩ : Mat A) (⟨n, Q⟩ : Mat A))
        + cls (Mat.kron (⟨n, E⟩ : Mat A) (⟨n, E⟩ : Mat A)) := by
  have hpq : (Mat.kron (⟨n, P⟩ : Mat A) (⟨n, Q⟩ : Mat A)).IsIdem :=
    Mat.kron_idem (fun x y : A => mul_comm x y) hP hQ
  have hee : (Mat.kron (⟨n, E⟩ : Mat A) (⟨n, E⟩ : Mat A)).IsIdem :=
    Mat.kron_idem (fun x y : A => mul_comm x y) hE hE
  have hQ1 : (⟨n * n + n * n, diskQ1 P Q E⟩ : Mat A)
      = Mat.sum (Mat.kron (⟨n, P⟩ : Mat A) (⟨n, Q⟩ : Mat A))
                (Mat.kron (⟨n, E⟩ : Mat A) (⟨n, E⟩ : Mat A)) := rfl
  rw [hQ1, cls_sum (p := Mat.kron (⟨n, P⟩ : Mat A) (⟨n, Q⟩ : Mat A))
    (q := Mat.kron (⟨n, E⟩ : Mat A) (⟨n, E⟩ : Mat A)) hpq hee]

/-- The class of `Q₂ = P ⊗ E ⊕ E ⊗ Q`. -/
private lemma cls_diskQ2 {A : Type} [CommRing A] (n : ℕ)
    (P Q E : Matrix (Fin n) (Fin n) A) (hP : P * P = P) (hQ : Q * Q = Q) (hE : E * E = E) :
    cls (⟨n * n + n * n, diskQ2 P Q E⟩ : Mat A)
      = cls (Mat.kron (⟨n, P⟩ : Mat A) (⟨n, E⟩ : Mat A))
        + cls (Mat.kron (⟨n, E⟩ : Mat A) (⟨n, Q⟩ : Mat A)) := by
  have hpe : (Mat.kron (⟨n, P⟩ : Mat A) (⟨n, E⟩ : Mat A)).IsIdem :=
    Mat.kron_idem (fun x y : A => mul_comm x y) hP hE
  have heq : (Mat.kron (⟨n, E⟩ : Mat A) (⟨n, Q⟩ : Mat A)).IsIdem :=
    Mat.kron_idem (fun x y : A => mul_comm x y) hE hQ
  have hQ2 : (⟨n * n + n * n, diskQ2 P Q E⟩ : Mat A)
      = Mat.sum (Mat.kron (⟨n, P⟩ : Mat A) (⟨n, E⟩ : Mat A))
                (Mat.kron (⟨n, E⟩ : Mat A) (⟨n, Q⟩ : Mat A)) := rfl
  rw [hQ2, cls_sum (p := Mat.kron (⟨n, P⟩ : Mat A) (⟨n, E⟩ : Mat A))
    (q := Mat.kron (⟨n, E⟩ : Mat A) (⟨n, Q⟩ : Mat A)) hpe heq]

theorem hk_diskW_class_prod {A : Type} [CommRing A] (n : ℕ)
    (P Q E : Matrix (Fin n) (Fin n) A)
    (hP : P * P = P) (hQ : Q * Q = Q) (hE : E * E = E)
    {c s : A} (hcs : c * c + s * s = 1)
    (μ : K0 A →+ K0 A →+ K0 A) (hμ : IsK0Mul μ) :
    cls (⟨(n * n + n * n) + (n * n + n * n), diskW P Q E c s⟩ : Mat A)
        - cls (diagMat A (2 * (n * n)) (4 * (n * n)))
      = μ (cls (⟨n, P⟩ : Mat A) - cls (⟨n, E⟩ : Mat A))
          (cls (⟨n, Q⟩ : Mat A) - cls (⟨n, E⟩ : Mat A)) := by
  have hexp : μ (cls (⟨n, P⟩ : Mat A) - cls (⟨n, E⟩ : Mat A))
        (cls (⟨n, Q⟩ : Mat A) - cls (⟨n, E⟩ : Mat A))
      = (cls (Mat.kron (⟨n, P⟩ : Mat A) (⟨n, Q⟩ : Mat A))
          - cls (Mat.kron (⟨n, P⟩ : Mat A) (⟨n, E⟩ : Mat A)))
        - (cls (Mat.kron (⟨n, E⟩ : Mat A) (⟨n, Q⟩ : Mat A))
          - cls (Mat.kron (⟨n, E⟩ : Mat A) (⟨n, E⟩ : Mat A))) := by
    rw [prod_sub_sub,
      IsK0Mul_cls (R := A) hμ (p := (⟨n, P⟩ : Mat A)) (q := (⟨n, Q⟩ : Mat A)) hP hQ,
      IsK0Mul_cls (R := A) hμ (p := (⟨n, P⟩ : Mat A)) (q := (⟨n, E⟩ : Mat A)) hP hE,
      IsK0Mul_cls (R := A) hμ (p := (⟨n, E⟩ : Mat A)) (q := (⟨n, Q⟩ : Mat A)) hE hQ,
      IsK0Mul_cls (R := A) hμ (p := (⟨n, E⟩ : Mat A)) (q := (⟨n, E⟩ : Mat A)) hE hE]
  have hdiag : cls (diagMat A (2 * (n * n)) (4 * (n * n)))
      = cls (diagMat A (n * n + n * n) ((n * n + n * n) + (n * n + n * n))) :=
    cls_diagMat_cast (R := A) (r := 2 * (n * n)) (r' := n * n + n * n)
      (m := 4 * (n * n)) (k := (n * n + n * n) + (n * n + n * n)) (by ring) (by ring)
  rw [diskW_class (R := A) P Q E hP hQ hE hcs, hdiag, cls_diskQ1 n P Q E hP hQ hE,
    cls_diskQ2 n P Q E hP hQ hE, hexp]
  abel

end Work.KT.HopfK
