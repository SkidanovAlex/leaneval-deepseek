import Mathlib
import Submission.Work.DSTR.M110.SplitCase.StdCase
import Submission.Work.DSTR.M110.SplitCase.ConjReduce

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace Work.DSTR.M110

open Work.AUTL2 Work.DSTR.M110.SplitAux

theorem splitCase (p k r : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    [DecidableEq (GaloisField p k)] (hrp : r.Prime) (hro : Odd r)
    (Q : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (hL : Work.AUTL2.pslImage (GaloisField p k) ≤ Q)
    (hQ : Q ≤ Work.AUTL2.pgammaL (GaloisField p k))
    (t : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))
    (htQ : t ∈ Q) (ht2 : orderOf t = 2) (htpgl : t ∈ Work.AUTL2.pglImage (GaloisField p k))
    (a b : Work.AUTL2.P1 (GaloisField p k)) (hab : a ≠ b) (ha : t a = a) (hb : t b = b)
    (N : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (hNle : N ≤ Q)
    (hNcent : N ≤ Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))))
    (hNnorm : ∀ c : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)),
        c ∈ Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) → c ∈ Q →
        ∀ x ∈ N, c * x * c⁻¹ ∈ N)
    (hNr : IsPGroup r N) :
    N ≤ Work.AUTL2.pslImage (GaloisField p k) := by
  haveI : Fact r.Prime := ⟨hrp⟩
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  obtain ⟨g, hgmem, hga, hgb, hgt⟩ :=
    exists_conj_negPerm p k hp hq t htpgl ht2 a b hab ha hb
  have hgpg : g ∈ pgammaL (GaloisField p k) :=
    (le_sup_left : pglImage (GaloisField p k) ≤ pgammaL (GaloisField p k)) hgmem
  have hginv : g⁻¹ ∈ pgammaL (GaloisField p k) := Subgroup.inv_mem _ hgpg
  let φ : Equiv.Perm (P1 (GaloisField p k)) ≃* Equiv.Perm (P1 (GaloisField p k)) :=
    MulAut.conj g
  have hφapply : ∀ x : Equiv.Perm (P1 (GaloisField p k)), φ x = g * x * g⁻¹ :=
    fun x => MulAut.conj_apply g x
  let Q' : Subgroup (Equiv.Perm (P1 (GaloisField p k))) := Q.map φ.toMonoidHom
  let N' : Subgroup (Equiv.Perm (P1 (GaloisField p k))) := N.map φ.toMonoidHom
  have hpsl' : pslImage (GaloisField p k) ≤ Q' := by
    intro x hx
    refine ⟨g⁻¹ * x * g, hL ?_, ?_⟩
    · exact Normalizer.conj_mem_pslImage (GaloisField p k)
        (Galois.pgammaL_le_normalizer_pslImage (GaloisField p k) hginv) hx
    · show φ (g⁻¹ * x * g) = x
      rw [hφapply]
      group
  have hQ'le : Q' ≤ pgammaL (GaloisField p k) := by
    rintro x ⟨y, hy, rfl⟩
    show φ y ∈ pgammaL (GaloisField p k)
    rw [hφapply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgpg (hQ hy)) (Subgroup.inv_mem _ hgpg)
  have hN'le : N' ≤ Q' := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, hNle hy, rfl⟩
  have hN'cent : N' ≤ Subgroup.centralizer ({negPerm (GaloisField p k)} : Set _) := by
    rintro x ⟨y, hy, rfl⟩
    refine (Subgroup.mem_centralizer_iff).mpr ?_
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hycomm : t * y = y * t :=
      (Subgroup.mem_centralizer_iff.mp (hNcent hy)) t (Set.mem_singleton t)
    show negPerm (GaloisField p k) * φ y = φ y * negPerm (GaloisField p k)
    rw [← hgt, hφapply]
    rw [show (g * t * g⁻¹) * (g * y * g⁻¹) = g * (t * y) * g⁻¹ by group,
      show (g * y * g⁻¹) * (g * t * g⁻¹) = g * (y * t) * g⁻¹ by group, hycomm]
  have hN'norm : ∀ c : Equiv.Perm (P1 (GaloisField p k)),
      c ∈ Subgroup.centralizer ({negPerm (GaloisField p k)} : Set _) → c ∈ Q' →
      ∀ x ∈ N', c * x * c⁻¹ ∈ N' := by
    intro c hc hcQ x hxN'
    obtain ⟨c₀, hc₀Q, hc₀eq⟩ := hcQ
    obtain ⟨n, hnN, hnxe⟩ := hxN'
    have hc₀cent : c₀ ∈ Subgroup.centralizer ({t} : Set _) := by
      refine (Subgroup.mem_centralizer_iff).mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      have h2 := (Subgroup.mem_centralizer_iff.mp hc) (negPerm (GaloisField p k))
        (Set.mem_singleton _)
      have h3 : φ h * φ c₀ = φ c₀ * φ h := by
        rw [← hc₀eq, ← hgt, ← hh] at h2
        rwa [← hφapply h] at h2
      exact φ.injective (by rw [map_mul, map_mul]; exact h3)
    refine ⟨c₀ * n * c₀⁻¹, hNnorm c₀ hc₀cent hc₀Q n hnN, ?_⟩
    rw [map_mul, map_mul, map_inv, hc₀eq, hnxe]
  have hNr' : IsPGroup r N' := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hNr
    refine (IsPGroup.iff_card).mpr ⟨m, ?_⟩
    rw [← hm]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective N φ.toMonoidHom φ.injective).symm
  have hstd := splitCase_std p k r hp hq hrp hro Q' hpsl' hQ'le N'
    hN'le hN'cent hN'norm hNr'
  intro n hn
  have hn' : φ n ∈ pslImage (GaloisField p k) := hstd ⟨n, hn, rfl⟩
  have hback : g⁻¹ * φ n * g ∈ pslImage (GaloisField p k) :=
    Normalizer.conj_mem_pslImage (GaloisField p k)
      (Galois.pgammaL_le_normalizer_pslImage (GaloisField p k) hginv) hn'
  convert hback using 1
  rw [hφapply]
  group

end Work.DSTR.M110
