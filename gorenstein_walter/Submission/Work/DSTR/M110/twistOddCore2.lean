import Mathlib
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Galois.decomposition
import Submission.Work.DSTR.M110.SplitCase.GaloisPart
import Submission.Work.DSTR.M110.Mobius
import Submission.Work.DSTR.M110.Stabilizer
import Submission.Work.DSTR.M110.Normalizer.Defs
import Submission.Work.DSTR.M110.Normalizer.le_pgammaL
import Submission.Work.DSTR.M110.Aut.pglIndex
import Submission.Work.DSTR.M110.twistTranslCentralizer
import Submission.Work.DSTR.M110.twistOuterInvolutionFixedPoint
import Submission.Work.DSTR.M110.twistCentralOdd

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110

open Work.AUTL2

/-! ## Elementary facts about `pglImage` / `pslImage`

(Reproved here because `Submission.Work.DSTR.M110.twistBasics`, where they also live, pulls in
modules that are not free of unproved placeholders.) -/

/-- An odd-order element of `pglImage F` lies in `pslImage F`
(`PGL(2,F)/PSL(2,F)` has exponent two for `F` finite of odd characteristic). -/
lemma odd_mem_pslImage_of_mem_pglImage {p k : ℕ} [Fact p.Prime]
    [DecidableEq (GaloisField p k)] {x : Equiv.Perm (P1 (GaloisField p k))}
    (hx : x ∈ pglImage (GaloisField p k)) (hodd : Odd (orderOf x)) :
    x ∈ pslImage (GaloisField p k) := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  set x : Equiv.Perm (P1 (GaloisField p k)) :=
    pglHom _ (Matrix.ProjGenLinGroup.mk B) with hxdef
  have hsq : x * x ∈ pslImage (GaloisField p k) := by
    have hxx : x * x = pglHom _ (Matrix.ProjGenLinGroup.mk (B * B)) := by
      rw [hxdef, ← map_mul, ← map_mul]
    rw [hxx, Work.AUTL2.Aut.mem_pslImage_iff_isSquare_det]
    exact ⟨B.det, by rw [map_mul]⟩
  have hm : x ^ orderOf x = 1 := pow_orderOf_eq_one x
  obtain ⟨s, hs⟩ := hodd
  have h2 : 2 * ((orderOf x + 1) / 2) = orderOf x + 1 := by omega
  have hsplit : x = (x * x) ^ ((orderOf x + 1) / 2) := by
    calc x = x ^ (orderOf x + 1) := by rw [pow_succ, hm, one_mul]
      _ = x ^ (2 * ((orderOf x + 1) / 2)) := by rw [h2]
      _ = (x * x) ^ ((orderOf x + 1) / 2) := by rw [pow_mul, pow_two]
  rw [hsplit]
  exact Subgroup.pow_mem _ hsq _

/-- `pglImage F` is normal in `pgammaL F`. -/
lemma conj_mem_pglImage' {p k : ℕ} [Fact p.Prime] [DecidableEq (GaloisField p k)]
    {g y : Equiv.Perm (P1 (GaloisField p k))} (hg : g ∈ pgammaL (GaloisField p k))
    (hy : y ∈ pglImage (GaloisField p k)) : g * y * g⁻¹ ∈ pglImage (GaloisField p k) := by
  have hnorm : pgammaL (GaloisField p k) ≤
      Subgroup.normalizer (pglImage (GaloisField p k) : Set _) := by
    rw [pgammaL]
    exact sup_le Subgroup.le_normalizer (Galois.galSub_le_normalizer_pglImage _)
  exact (Subgroup.le_normalizer_iff.mp hnorm) g hg y hy

/-- `pslImage F` is normal in `pgammaL F`. -/
lemma conj_mem_pslImage' {p k : ℕ} [Fact p.Prime] [DecidableEq (GaloisField p k)]
    {g y : Equiv.Perm (P1 (GaloisField p k))} (hg : g ∈ pgammaL (GaloisField p k))
    (hy : y ∈ pslImage (GaloisField p k)) : g * y * g⁻¹ ∈ pslImage (GaloisField p k) :=
  (Subgroup.le_normalizer_iff.mp (Galois.pgammaL_le_normalizer_pslImage _)) g hg y hy

/-- The conjugation automorphism of a group, evaluated (`MonoidHom`-coercion form). -/
lemma mulAut_conj_apply_hom {G : Type*} [Group G] (g x : G) :
    (MulAut.conj g : G →* G) x = g * x * g⁻¹ := by
  rw [show (MulAut.conj g : G →* G) x = (MulAut.conj g : G ≃* G) x from rfl,
    MulAut.conj_apply]

/-! ## The twist case, with `t` fixing `∞` -/

/-- **The twist case of the odd core lemma**, assuming the outer involution `t` fixes `∞`.

`L := pslImage F ⊓ C(t)` is the centralizer in `PSL(2,q)` of the twist `t`; every odd-order
normal subgroup of a group between `L` and `C(t)` is trivial (`twistCentralOdd`), so
`N ⊓ pglImage = ⊥`.  Hence every element of `N` commutes with `L`, in particular with the group
of translations centralised by `t`, and `twistTranslCentralizer` puts it in `pglImage`.  As `N`
has odd order, `N ≤ pslImage`. -/
theorem twistOddCore2_aux (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    [DecidableEq (GaloisField p k)] (t : Equiv.Perm (P1 (GaloisField p k)))
    (htG : t ∈ pgammaL (GaloisField p k)) (htinf : t ∞ = ∞)
    (ht2 : orderOf t = 2) (htnpgl : t ∉ pglImage (GaloisField p k))
    (K : Subgroup (Equiv.Perm (P1 (GaloisField p k))))
    (hKle : K ≤ pgammaL (GaloisField p k))
    (hKcent : K ≤ Subgroup.centralizer ({t} : Set (Equiv.Perm (P1 (GaloisField p k)))))
    (hKge : pslImage (GaloisField p k) ⊓
        Subgroup.centralizer ({t} : Set (Equiv.Perm (P1 (GaloisField p k)))) ≤ K)
    (N : Subgroup (Equiv.Perm (P1 (GaloisField p k))))
    (hNK : N ≤ K)
    (hNnormal : ∀ c : Equiv.Perm (P1 (GaloisField p k)), c ∈ K → ∀ x ∈ N, c * x * c⁻¹ ∈ N)
    (hNodd : Odd (Nat.card N)) :
    N ≤ pslImage (GaloisField p k) := by
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  -- `M = N ⊓ pglImage`
  set M : Subgroup (Equiv.Perm (P1 (GaloisField p k))) :=
    N ⊓ pglImage (GaloisField p k) with hMdef
  -- `M` consists of odd-order elements of `N ⊓ pglImage`, hence lies in `L = pslImage ⊓ C(t)`
  have hMle_psl : M ≤ pslImage (GaloisField p k) := by
    intro m hm
    have hmN : m ∈ N := (Subgroup.mem_inf.mp hm).1
    have hmpgl : m ∈ pglImage (GaloisField p k) := (Subgroup.mem_inf.mp hm).2
    have hoddm : Odd (orderOf m) := by
      refine hNodd.of_dvd_nat ?_
      have h1 : orderOf (⟨m, hmN⟩ : ↥N) ∣ Nat.card ↥N := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk] at h1
    exact odd_mem_pslImage_of_mem_pglImage hmpgl hoddm
  have hMle_L : M ≤ pslImage (GaloisField p k) ⊓
      Subgroup.centralizer ({t} : Set (Equiv.Perm (P1 (GaloisField p k)))) := by
    refine le_inf hMle_psl ?_
    intro m hm
    exact hKcent (hNK (Subgroup.mem_inf.mp hm).1)
  -- `M` is normalised by `L`
  have hMnorm : ∀ c : Equiv.Perm (P1 (GaloisField p k)),
      c ∈ pslImage (GaloisField p k) ⊓
        Subgroup.centralizer ({t} : Set (Equiv.Perm (P1 (GaloisField p k)))) →
      ∀ x ∈ M, c * x * c⁻¹ ∈ M := by
    intro c hc x hx
    have hcK : c ∈ K := hKge hc
    refine Subgroup.mem_inf.mpr ⟨hNnormal c hcK x hx.1, ?_⟩
    exact conj_mem_pglImage' (hKle hcK) hx.2
  have hModd : Odd (Nat.card M) :=
    hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hMbot : M = ⊥ :=
    twistCentralOdd p k hp hq t htG ht2 htnpgl M hMle_L hMnorm hModd
  -- hence `N` centralises `L`
  have hcommL : ∀ n ∈ N, ∀ l ∈ pslImage (GaloisField p k) ⊓
      Subgroup.centralizer ({t} : Set (Equiv.Perm (P1 (GaloisField p k)))),
      n * l = l * n := by
    intro n hn l hl
    have hlK : l ∈ K := hKge hl
    have hlG : l ∈ pgammaL (GaloisField p k) := hKle hlK
    have hnG : n ∈ pgammaL (GaloisField p k) := hKle (hNK hn)
    have hlN : l * n * l⁻¹ ∈ N := hNnormal l hlK n hn
    have hmemN : l * n * l⁻¹ * n⁻¹ ∈ N :=
      Subgroup.mul_mem _ hlN (Subgroup.inv_mem _ hn)
    have hmemG : l * n * l⁻¹ * n⁻¹ ∈ pgammaL (GaloisField p k) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hlG hnG)
        (Subgroup.inv_mem _ hlG)) (Subgroup.inv_mem _ hnG)
    have hmem : l * n * l⁻¹ * n⁻¹ ∈ M := by
      refine Subgroup.mem_inf.mpr ⟨hmemN, ?_⟩
      have hl1 : SplitAux.galMap (GaloisField p k) ⟨l, hlG⟩ = 1 :=
        (SplitAux.galPart_eq_one_iff (GaloisField p k) ⟨l, hlG⟩).mpr
          (pslImage_le_pglImage (GaloisField p k) hl.1)
      have hprod : (⟨l * n * l⁻¹ * n⁻¹, hmemG⟩ : ↥(pgammaL (GaloisField p k))) =
          ⟨l, hlG⟩ * ⟨n, hnG⟩ * ⟨l, hlG⟩⁻¹ * ⟨n, hnG⟩⁻¹ := by
        ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have hgal : SplitAux.galMap (GaloisField p k) ⟨l * n * l⁻¹ * n⁻¹, hmemG⟩ = 1 := by
        rw [hprod, map_mul, map_mul, map_mul, map_inv, map_inv, hl1]
        simp
      exact (SplitAux.galPart_eq_one_iff (GaloisField p k) _).mp hgal
    rw [hMbot] at hmem
    have h1 : l * n * l⁻¹ * n⁻¹ = 1 := by simpa using hmem
    have h2 : l * n * l⁻¹ = n := mul_inv_eq_one.mp h1
    have h3 : l * n = n * l := mul_inv_eq_iff_eq_mul.mp h2
    exact h3.symm
  -- every element of `N` centralises the translations centralised by `t`
  intro n hn
  have hnG : n ∈ pgammaL (GaloisField p k) := hKle (hNK hn)
  have hoddn : Odd (orderOf n) := by
    refine hNodd.of_dvd_nat ?_
    have h1 : orderOf (⟨n, hn⟩ : ↥N) ∣ Nat.card ↥N := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk] at h1
  have hcommV : ∀ c : GaloisField p k,
      transl (GaloisField p k) c * t = t * transl (GaloisField p k) c →
      n * transl (GaloisField p k) c = transl (GaloisField p k) c * n := by
    intro c hc
    refine hcommL n hn _ (Subgroup.mem_inf.mpr ⟨transl_mem _ c, ?_⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mpr hc
  exact odd_mem_pslImage_of_mem_pglImage
    (twistTranslCentralizer p k hp hq t n htG htinf ht2 htnpgl hnG hoddn hcommV) hoddn

/-! ## The twist case in general -/

/-- **The "twist" corner case is degenerate, version with `pslImage ⊓ C(t) ≤ K`.**

`t ∈ PΓL(2,q) \ PGL(2,q)` with `t² = 1`, `K ≤ C(t) ∩ PΓL(2,q)` containing `L = PSL(2,q) ∩ C(t)`,
and `N ◁ K` of odd order.  Then `N ≤ PSL(2,q)`.

Since `t` has a fixed point on `ℙ¹(F)` (`twistOuterInvolutionFixedPoint`) we may conjugate
`(t, K, N)` by an element of `pslImage` moving that fixed point to `∞`, which reduces to
`twistOddCore2_aux`. -/
theorem twistOddCore2 (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    [DecidableEq (GaloisField p k)] (t : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))
    (htG : t ∈ Work.AUTL2.pgammaL (GaloisField p k))
    (ht2 : orderOf t = 2) (htnpgl : t ∉ Work.AUTL2.pglImage (GaloisField p k))
    (K : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (hKle : K ≤ Work.AUTL2.pgammaL (GaloisField p k))
    (hKcent : K ≤ Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))))
    (hKge : Work.AUTL2.pslImage (GaloisField p k) ⊓
        Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) ≤ K)
    (N : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (hNK : N ≤ K)
    (hNnormal : ∀ c : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)), c ∈ K → ∀ x ∈ N, c * x * c⁻¹ ∈ N)
    (hNodd : Odd (Nat.card N)) :
    N ≤ Work.AUTL2.pslImage (GaloisField p k) := by
  classical
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  -- a fixed point of `t`, moved to `∞` by an element of `pslImage`
  obtain ⟨y, hy⟩ := twistOuterInvolutionFixedPoint p k hp hq t htG ht2 htnpgl
  obtain ⟨g, hgmem, hgy⟩ := exists_pslImage_map_to_infty (GaloisField p k) y
  have hgG : g ∈ pgammaL (GaloisField p k) :=
    Subgroup.mem_sup_left (pslImage_le_pglImage (GaloisField p k) hgmem)
  -- conjugate everything by `g`
  set e : MulAut (Equiv.Perm (P1 (GaloisField p k))) := MulAut.conj g with he
  have he_apply : ∀ x : Equiv.Perm (P1 (GaloisField p k)),
      (e : Equiv.Perm (P1 (GaloisField p k)) →* Equiv.Perm (P1 (GaloisField p k))) x
        = g * x * g⁻¹ := by
    intro x
    rw [he]
    exact mulAut_conj_apply_hom g x
  set t' : Equiv.Perm (P1 (GaloisField p k)) := e t with ht'def
  have ht'_eq : t' = g * t * g⁻¹ := by rw [ht'def, he]; exact MulAut.conj_apply g t
  set K' : Subgroup (Equiv.Perm (P1 (GaloisField p k))) :=
    K.map (e : Equiv.Perm (P1 (GaloisField p k)) →*
      Equiv.Perm (P1 (GaloisField p k))) with hK'def
  set N' : Subgroup (Equiv.Perm (P1 (GaloisField p k))) :=
    N.map (e : Equiv.Perm (P1 (GaloisField p k)) →*
      Equiv.Perm (P1 (GaloisField p k))) with hN'def
  have hmemK' : ∀ x : Equiv.Perm (P1 (GaloisField p k)), x ∈ K' ↔ g⁻¹ * x * g ∈ K := by
    intro x
    rw [hK'def, Subgroup.mem_map]
    constructor
    · rintro ⟨c, hc, hcx⟩
      have h1 : g * c * g⁻¹ = x := by rw [← hcx, he_apply]
      have h2 : g⁻¹ * x * g = c := by rw [← h1]; group
      rwa [h2]
    · intro hx
      refine ⟨g⁻¹ * x * g, hx, ?_⟩
      rw [he_apply]
      group
  have hmemN' : ∀ x : Equiv.Perm (P1 (GaloisField p k)), x ∈ N' ↔ g⁻¹ * x * g ∈ N := by
    intro x
    rw [hN'def, Subgroup.mem_map]
    constructor
    · rintro ⟨c, hc, hcx⟩
      have h1 : g * c * g⁻¹ = x := by rw [← hcx, he_apply]
      have h2 : g⁻¹ * x * g = c := by rw [← h1]; group
      rwa [h2]
    · intro hx
      refine ⟨g⁻¹ * x * g, hx, ?_⟩
      rw [he_apply]
      group
  have htg : g⁻¹ ∞ = y := by
    have := congrArg (fun z => g⁻¹ z) hgy
    simpa using this.symm
  have ht'inf : t' ∞ = ∞ := by
    rw [ht'_eq]
    simp only [Equiv.Perm.mul_apply, htg, hy, hgy]
  have ht2' : t * t = 1 := by simpa [ht2, pow_two] using pow_orderOf_eq_one t
  have ht'2 : orderOf t' = 2 := by
    have h2 : t' * t' = 1 := by
      rw [ht'_eq]
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [ht2']; group
    have hne : t' ≠ 1 := by
      intro h
      have h1 : t = 1 := by
        have h2' : (g * t * g⁻¹) = 1 := by rw [← ht'_eq]; exact h
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [h2']; group
      have hord := ht2
      rw [h1, orderOf_one] at hord
      exact absurd hord (by norm_num)
    exact orderOf_eq_prime (by rwa [pow_two]) hne
  have ht'G : t' ∈ pgammaL (GaloisField p k) := by
    rw [ht'_eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgG htG) (Subgroup.inv_mem _ hgG)
  have ht'npg : t' ∉ pglImage (GaloisField p k) := by
    intro h
    refine htnpgl ?_
    have h1 : g⁻¹ * t' * g ∈ pglImage (GaloisField p k) :=
      conj_mem_pglImage' (Subgroup.inv_mem _ hgG) h
    have h2 : g⁻¹ * t' * g = t := by rw [ht'_eq]; group
    rwa [h2] at h1
  have hK'le : K' ≤ pgammaL (GaloisField p k) := by
    intro x hx
    have h1 : g⁻¹ * x * g ∈ K := (hmemK' x).mp hx
    rw [← show g * (g⁻¹ * x * g) * g⁻¹ = x from by group]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgG (hKle h1)) (Subgroup.inv_mem _ hgG)
  have hK'cent : K' ≤ Subgroup.centralizer ({t'} : Set (Equiv.Perm (P1 (GaloisField p k)))) := by
    intro x hx
    have h1 : g⁻¹ * x * g ∈ K := (hmemK' x).mp hx
    have h2 : (g⁻¹ * x * g) * t = t * (g⁻¹ * x * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKcent h1)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [ht'_eq]
    calc x * (g * t * g⁻¹) = g * ((g⁻¹ * x * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by rw [h2]
      _ = (g * t * g⁻¹) * x := by group
  have hK'ge : pslImage (GaloisField p k) ⊓
      Subgroup.centralizer ({t'} : Set (Equiv.Perm (P1 (GaloisField p k)))) ≤ K' := by
    intro x hx
    have hxpsl : x ∈ pslImage (GaloisField p k) := (Subgroup.mem_inf.mp hx).1
    have hxcen : x * t' = t' * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
    have hconv : g⁻¹ * x * g ∈ pslImage (GaloisField p k) ⊓
        Subgroup.centralizer ({t} : Set (Equiv.Perm (P1 (GaloisField p k)))) := by
      refine Subgroup.mem_inf.mpr ⟨conj_mem_pslImage' (Subgroup.inv_mem _ hgG) hxpsl, ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [ht'_eq] at hxcen
      calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [← hxcen]
        _ = t * (g⁻¹ * x * g) := by group
    exact (hmemK' x).mpr (hKge hconv)
  have hN'K : N' ≤ K' := by
    intro x hx
    exact (hmemK' x).mpr (hNK ((hmemN' x).mp hx))
  have hN'normal : ∀ c : Equiv.Perm (P1 (GaloisField p k)), c ∈ K' → ∀ x ∈ N', c * x * c⁻¹ ∈ N' := by
    intro c hc x hx
    have hc1 : g⁻¹ * c * g ∈ K := (hmemK' c).mp hc
    have hx1 : g⁻¹ * x * g ∈ N := (hmemN' x).mp hx
    refine (hmemN' (c * x * c⁻¹)).mpr ?_
    have hcp : g⁻¹ * (c * x * c⁻¹) * g
        = (g⁻¹ * c * g) * (g⁻¹ * x * g) * (g⁻¹ * c * g)⁻¹ := by group
    rw [hcp]
    exact hNnormal _ hc1 _ hx1
  have hN'odd : Odd (Nat.card N') := by
    have hbij : Nat.card ↥N' = Nat.card ↥N :=
      Nat.card_congr
        { toFun := fun x => ⟨g⁻¹ * x.1 * g, (hmemN' x.1).mp x.2⟩
          invFun := fun y => ⟨g * y.1 * g⁻¹, (hmemN' _).mpr (by
            have : g⁻¹ * (g * y.1 * g⁻¹) * g = y.1 := by group
            rw [this]; exact y.2)⟩
          left_inv := by intro x; ext; group
          right_inv := by intro y; ext; group }
    rw [hbij]
    exact hNodd
  have hN'le : N' ≤ pslImage (GaloisField p k) :=
    twistOddCore2_aux p k hp hq t' ht'G ht'inf ht'2 ht'npg K' hK'le hK'cent hK'ge N' hN'K
      hN'normal hN'odd
  intro n hn
  have hn' : g * n * g⁻¹ ∈ N' := (hmemN' _).mpr (by
    have : g⁻¹ * (g * n * g⁻¹) * g = n := by group
    rw [this]; exact hn)
  have h1 : g * n * g⁻¹ ∈ pslImage (GaloisField p k) := hN'le hn'
  have h2 : g⁻¹ * (g * n * g⁻¹) * g ∈ pslImage (GaloisField p k) :=
    conj_mem_pslImage' (Subgroup.inv_mem _ hgG) h1
  have h3 : g⁻¹ * (g * n * g⁻¹) * g = n := by group
  rwa [h3] at h2

end Work.DSTR.M110
