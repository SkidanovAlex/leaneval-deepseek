import Mathlib.RingTheory.Polynomial.Resultant.Basic

open Polynomial
open scoped Matrix

namespace Commons.RingTheory.Polynomial

noncomputable section

private lemma sylvester_apply_eq {R : Type*} [CommRing R] (f g : R[X]) (m n : ℕ)
    (i j : Fin (m + n)) :
    (f.sylvester g m n) i j =
      (if (j : ℕ) < m then
          if (i : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + n) then g.coeff ((i : ℕ) - (j : ℕ)) else 0
        else
          if (i : ℕ) ∈ Set.Icc ((j : ℕ) - m) (((j : ℕ) - m) + m) then
            f.coeff ((i : ℕ) - ((j : ℕ) - m)) else 0) := by
  rw [Polynomial.sylvester, Matrix.of_apply]
  by_cases hjm : (j : ℕ) < m
  · have hjcast : j = Fin.castAdd n ⟨(j : ℕ), hjm⟩ := by
      ext; simp
    conv_lhs => rw [hjcast, Fin.addCases_left]
    simp [hjm]
  · have hge : m ≤ (j : ℕ) := le_of_not_gt hjm
    have hjnat : (j : ℕ) - m < n := by omega
    have hjcast : j = Fin.natAdd m ⟨(j : ℕ) - m, hjnat⟩ := by
      ext; simp [Nat.add_sub_of_le hge]
    conv_lhs => rw [hjcast, Fin.addCases_right]
    simp [hge]

private lemma sylvester_reindex {R : Type*} [CommRing R] (f g : R[X])
    (m n m' n' : ℕ) (hm : m = m') (hn : n = n') :
    (f.sylvester g m n).reindex (finCongr (by omega)) (finCongr (by omega)) = f.sylvester g m' n' := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [sylvester_apply_eq (f := f) (g := g) (m := m) (n := n)
    (i := (finCongr (by omega)).symm i) (j := (finCongr (by omega)).symm j)]
  rw [sylvester_apply_eq (f := f) (g := g) (m := m') (n := n') (i := i) (j := j)]
  simp only [finCongr_symm_apply_coe]
  split_ifs <;> simp [hm, hn] <;> omega

/-- The bottom row of `sylvesterDeriv`, as a function, is compatible with `φ`. -/
private lemma bottomRow_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (n np : ℕ) (hn : np = n) :
    (fun j : Fin (np - 1 + np) ↦
        if (j : ℕ) = np - 2 then (1 : S)
        else if (j : ℕ) = 2 * np - 2 then (np : S) else 0) =
      fun j : Fin (np - 1 + np) ↦
        φ (if ((finCongr (by omega : n - 1 + n = np - 1 + np)).symm j : ℕ) = n - 2 then (1 : R)
           else if ((finCongr (by omega : n - 1 + n = np - 1 + np)).symm j : ℕ) = 2 * n - 2
             then (n : R) else 0) := by
  ext j
  by_cases h1 : (j : ℕ) = np - 2
  · have hc1 : ((finCongr (by omega : n - 1 + n = np - 1 + np)).symm j : ℕ) = n - 2 := by
      simp [finCongr_symm_apply_coe, h1, hn]
    rw [apply_ite φ]
    simp [hc1, h1, hn]
  · by_cases h2 : (j : ℕ) = 2 * np - 2
    · have hc1 : ¬ ((finCongr (by omega : n - 1 + n = np - 1 + np)).symm j : ℕ) = n - 2 := by
        simp [finCongr_symm_apply_coe]; omega
      have hc2 : ((finCongr (by omega : n - 1 + n = np - 1 + np)).symm j : ℕ) = 2 * n - 2 := by
        simp [finCongr_symm_apply_coe, h2, hn]
      rw [apply_ite φ, apply_ite φ]
      simp [h1, h2, hc1, hc2, hn]
    · have hc1 : ¬ ((finCongr (by omega : n - 1 + n = np - 1 + np)).symm j : ℕ) = n - 2 := by
        simp [finCongr_symm_apply_coe]; omega
      have hc2 : ¬ ((finCongr (by omega : n - 1 + n = np - 1 + np)).symm j : ℕ) = 2 * n - 2 := by
        simp [finCongr_symm_apply_coe]; omega
      rw [apply_ite φ, apply_ite φ]
      simp [h1, h2, hc1, hc2, hn]

/-- `sylvesterDeriv` commutes with the matrix functor associated to a degree-preserving ring
homomorphism, up to the canonical reindexing of the matrix dimensions. -/
private lemma sylvesterDeriv_map_reindex {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {p : R[X]} (hdeg : (p.map φ).natDegree = p.natDegree) :
    ((φ.mapMatrix p.sylvesterDeriv).reindex
      (finCongr (by rw [hdeg])) (finCongr (by rw [hdeg]))) = (p.map φ).sylvesterDeriv := by
  by_cases h0 : p.natDegree = 0
  · simp [Polynomial.sylvesterDeriv, hdeg, h0]
  · have hnp : (p.map φ).natDegree ≠ 0 := by simpa [hdeg] using h0
    let n : ℕ := p.natDegree
    let np : ℕ := (p.map φ).natDegree
    have hnnp : np = n := by simpa [n, np] using hdeg
    let e : Fin (n - 1 + n) ≃ Fin (np - 1 + np) := finCongr (by omega)
    let A : Matrix (Fin (n - 1 + n)) (Fin (n - 1 + n)) R :=
      (derivative p).sylvester p (n - 1) n
    let r1 : Fin (n - 1 + n) := ⟨2 * n - 2, by omega⟩
    let br1 : Fin (n - 1 + n) → R := fun j ↦
      if (j : ℕ) = n - 2 then 1 else if (j : ℕ) = 2 * n - 2 then (n : R) else 0
    let B : Matrix (Fin (np - 1 + np)) (Fin (np - 1 + np)) S :=
      (map φ (derivative p)).sylvester (map φ p) (np - 1) np
    let r2 : Fin (np - 1 + np) := ⟨2 * np - 2, by omega⟩
    let br2 : Fin (np - 1 + np) → S := fun j ↦
      if (j : ℕ) = np - 2 then 1 else if (j : ℕ) = 2 * np - 2 then (np : S) else 0
    have hs1 : p.sylvesterDeriv = A.updateRow r1 br1 := by
      rw [Polynomial.sylvesterDeriv, dif_neg h0]
    have hs2 : (p.map φ).sylvesterDeriv = B.updateRow r2 br2 := by
      rw [Polynomial.sylvesterDeriv, dif_neg hnp, Polynomial.derivative_map]
    have heA : (A.map φ).reindex e e = B := by
      calc
        (A.map φ).reindex e e
            = (φ.mapMatrix A).reindex e e := by
                rw [← RingHom.mapMatrix_apply]
        _ = ((map φ (derivative p)).sylvester (map φ p) (n - 1) n).reindex e e := by
                congr 1
                simpa [A] using (Polynomial.sylvester_map_map (derivative p) p (n - 1) n φ).symm
        _ = (map φ (derivative p)).sylvester (map φ p) (np - 1) np := by
                simpa [e, hnnp] using
                  (sylvester_reindex (map φ (derivative p)) (map φ p) (n - 1) n (np - 1) np
                    (by omega) (by omega))
    have her : e r1 = r2 := by
      ext; simp [e, r1, r2]; omega
    have hbr : br2 = (fun j : Fin (np - 1 + np) ↦ φ (br1 (e.symm j))) := by
      have hb := bottomRow_map (R := R) (S := S) φ n np hnnp
      simpa [br2, br1, e] using hb
    calc
      (φ.mapMatrix p.sylvesterDeriv).reindex e e
          = (φ.mapMatrix (A.updateRow r1 br1)).reindex e e := by rw [hs1]
      _ = ((A.map φ).updateRow r1 (φ ∘ br1)).reindex e e := by
            rw [RingHom.mapMatrix_apply, Matrix.map_updateRow]
      _ = ((A.map φ).reindex e e).updateRow (e r1)
            (fun j : Fin (np - 1 + np) ↦ (φ ∘ br1) (e.symm j)) := by
            rw [Matrix.reindex_updateRow]
      _ = ((A.map φ).reindex e e).updateRow r2 br2 := by
            rw [her]
            change ((A.map φ).reindex e e).updateRow r2
              (fun j : Fin (np - 1 + np) ↦ φ (br1 (e.symm j))) =
              ((A.map φ).reindex e e).updateRow r2 br2
            rw [hbr.symm]
      _ = (p.map φ).sylvesterDeriv := by
            rw [heA, hs2]

/-- Determinants of `sylvesterDeriv` commute with a degree-preserving ring homomorphism. -/
private lemma sylvesterDeriv_det_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {p : R[X]} (hdeg : (p.map φ).natDegree = p.natDegree) :
    φ p.sylvesterDeriv.det = (p.map φ).sylvesterDeriv.det := by
  let e : Fin (p.natDegree - 1 + p.natDegree) ≃ Fin ((p.map φ).natDegree - 1 + (p.map φ).natDegree) :=
    finCongr (by rw [hdeg])
  calc
    φ p.sylvesterDeriv.det = (φ.mapMatrix p.sylvesterDeriv).det :=
      (RingHom.map_det φ p.sylvesterDeriv)
    _ = ((φ.mapMatrix p.sylvesterDeriv).reindex e e).det :=
      (Matrix.det_reindex_self e (φ.mapMatrix p.sylvesterDeriv)).symm
    _ = (p.map φ).sylvesterDeriv.det := by
      rw [sylvesterDeriv_map_reindex φ hdeg]

theorem discr_map_of_natDegree {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {p : R[X]} (hdeg : (p.map φ).natDegree = p.natDegree) :
    φ (Polynomial.discr p) = Polynomial.discr (p.map φ) := by
  have hφneg : φ (-1 : R) = (-1 : S) := by rw [map_neg, map_one]
  have hφs : φ ((-1 : R) ^ (p.natDegree * (p.natDegree - 1) / 2)) =
      (-1 : S) ^ ((p.map φ).natDegree * ((p.map φ).natDegree - 1) / 2) := by
    rw [map_pow, hφneg]
    congr 1
    rw [hdeg]
  rw [Polynomial.discr, Polynomial.discr, map_mul]
  rw [sylvesterDeriv_det_map φ hdeg]
  rw [← hφs]

end

end Commons.RingTheory.Polynomial
